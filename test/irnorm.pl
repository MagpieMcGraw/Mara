#!/usr/bin/perl
# irnorm.pl — canonical form of a Mara .ll file, for comparing codegen output
# modulo naming: inside each function, locals and labels are renamed by order
# of first appearance (%v0, %v1, ...); string globals are replaced by their
# contents. Named types (%class.X = type ...) are left alone.
#
# Before renaming, each function drops what can't change what it does, one
# rule each:
#   - a block no branch reaches from the entry;
#   - a store the next instruction overwrites: same type, same pointer (after
#     only address arithmetic);
#   - a constant's width changed, which is that constant at the new width,
#     and integer arithmetic of constants, which is its result; a pointer
#     bitcast to a pointer, which is that pointer;
#   - address arithmetic whose shape can't matter: `inbounds`, a constant
#     index's width (it is sign-extended to the pointer's: `i32 1` and
#     `i64 1` step alike), an unused getelementptr, a chain of them folded
#     into one, where one is computed (a copy just before each use);
#   - a zeroing memset the next instruction repeats, or overwrites with a
#     memcpy of the same size (after only address arithmetic); and one of no
#     more than the memset just before it zeroed at the same pointer;
#   - a slot stored once, with a constant, before each of its loads (the
#     store dominates them), which is that constant (see forward_constants);
#   - an alloca nothing reads (only stored into), with its stores; a load
#     nothing uses;
#   - the order of the entry block's allocas, and of any block's leading run of
#     them (by first use);
#   - then, a string constant nothing references, and their order.
# Usage: irnorm.pl file.ll > file.norm
use strict; use warnings;
my @lines = <>;
s/\r$// for @lines;
my (%str, %type);
for (@lines) {
    $str{$1}  = $2 if /^(@\.[\w.]*str\.[\w]+) = private unnamed_addr constant (.*)$/;
    $type{$1} = 1  if /^(%[-\w.\$]+) = type /;
}

# The function bodies, cleaned; everything else as it is.
my (@out, @body);
my $in_body = 0;
for (@lines) {
    if ($in_body && /^}/) { push @out, clean(@body), $_; @body = (); $in_body = 0; next; }
    if ($in_body)         { push @body, $_; next; }
    push @out, $_;
    $in_body = 1 if /^define /;
}

# A string constant nothing references any more (its only use was in a block
# dropped above) is no part of what the module does.
my %ref;
for (@out) {
    next if /^@\.[\w.]*str\.[\w]+ = private unnamed_addr constant/;
    $ref{$1} = 1 while /(@\.[\w.]*str\.[\w]+)/g;
}
@out = grep { !(/^(@\.[\w.]*str\.[\w]+) = private unnamed_addr constant/ && !$ref{$1}) } @out;
# Their order says nothing either (each is named by its contents): sorted.
my @at_str = grep { $out[$_] =~ /^@\.[\w.]*str\.[\w]+ = private unnamed_addr constant/ } 0 .. $#out;
@out[@at_str] = sort @out[@at_str];

my ($in_fn, %map, $n) = (0);
for (@out) {
    if (/^define /) { $in_fn = 1; %map = (); $n = 0; }
    if ($in_fn) {
        s/^([-\w.\$]+):/($map{$1} \/\/= "v" . $n++) . ":"/e;          # label definition
        s/%([-a-zA-Z\$._][-\w.\$]*|\d+)/
            exists $type{"%$1"} ? "%$1" : "%" . ($map{$1} \/\/= "v" . $n++)/gex;
    }
    $in_fn = 0 if /^}/;
    # After renaming, so a string's own %s / %d stay as written.
    s/(@\.[\w.]*str\.[\w]+)/exists $str{$1} ? "\@STR<$str{$1}>" : $1/ge;
}
print @out;

# A function's body lines, less its unreachable blocks and overwritten stores.
sub clean {
    my @lines = @_;
    # Blocks: the entry (first) and each label's.
    my (@blocks, %at);
    for (@lines) {
        if (!@blocks || /^([-\w.\$]+):/) {
            my $name = /^([-\w.\$]+):/ ? $1 : "";
            push @blocks, { name => $name, lines => [] };
            $at{$name} = $#blocks if $name ne "";
        }
        push @{ $blocks[-1]{lines} }, $_;
    }
    # Reachable from the entry, through each block's branch targets.
    my %seen = (0 => 1);
    my @todo = (0);
    while (@todo) {
        my $b = pop @todo;
        for my $line (@{ $blocks[$b]{lines} }) {
            next unless $line =~ /^\s+(br|switch|i\d+ -?\d+, label)\b/;
            while ($line =~ /label %([-\w.\$]+)/g) {
                my $t = $at{$1};
                next if !defined $t || $seen{$t}++;
                push @todo, $t;
            }
        }
    }
    my @kept;
    for my $i (0 .. $#blocks) {
        next unless $seen{$i};
        push @kept, @{ $blocks[$i]{lines} };
    }

    my @l = drop_overwritten(drop_unread(simplify_geps(fold_widths(@kept))));
    # A slot's one store, once the stores overwritten are gone; what it
    # forwards may fold, and leaves the slot unread.
    @l = drop_unread(fold_widths(forward_constants(@l)));
    return order_allocas(simplify_geps(@l));   # (again: what a dropped memset addressed)
}

# A constant's width changed (`trunc i64 0 to i32`, `fptrunc double 0.5 to
# float`) is the constant itself at the new width, when it fits exactly, and
# integer arithmetic of constants (`shl i64 1, 10`) is its result: its uses
# take the constant.
sub fold_widths {
    my @lines = @_;
    # Folding one can make another's operands constants: again, until none.
    while (1) {
        my %const;
        for (@lines) {
            if (/^\s+(%[-\w.\$]+) = (fptrunc double|fpext float) (0x[0-9A-Fa-f]{16}) to (float|double)$/) {
                my ($name, $c) = ($1, $3);
                my $d = unpack('d>', pack('H16', substr($c, 2)));
                $const{$name} = $c if $2 eq 'fpext float' || unpack('f', pack('f', $d)) == $d;
                next;
            }
            # Integer arithmetic of two constants (`shl i64 1, 10`): its result,
            # while it stays well inside the width.
            if (/^\s+(%[-\w.\$]+) = (shl|add|sub|mul|and|or|xor) i(\d+) (-?\d+), (-?\d+)$/) {
                my ($name, $op, $bits, $a, $b) = ($1, $2, $3, $4 + 0, $5 + 0);
                next if $op eq 'shl' && ($b < 0 || $b > 52);
                my $x = $op eq 'shl' ? $a * 2 ** $b : $op eq 'add' ? $a + $b : $op eq 'sub' ? $a - $b
                      : $op eq 'mul' ? $a * $b : $op eq 'and' ? ($a & $b) : $op eq 'or' ? ($a | $b) : ($a ^ $b);
                next if $a < 0 || $b < 0 and $op =~ /^(and|or|xor)$/;
                my $lim = $bits < 53 ? 2 ** ($bits - 1) : 2 ** 52;
                $const{$name} = $x if $x < $lim && $x >= -$lim;
                next;
            }
            # Float arithmetic of two constants (`fmul double PI, 2.0`): its
            # result, rounded to single for a float (the double result rounds
            # to the single one: a double holds over twice the digits).
            if (/^\s+(%[-\w.\$]+) = (fadd|fsub|fmul|fdiv) (double|float) (0x[0-9A-Fa-f]{16}), (0x[0-9A-Fa-f]{16})$/) {
                my ($name, $op, $ty) = ($1, $2, $3);
                my ($a, $b) = map { unpack('d>', pack('H16', substr($_, 2))) } ($4, $5);
                next if $op eq 'fdiv' && $b == 0;
                my $x = $op eq 'fadd' ? $a + $b : $op eq 'fsub' ? $a - $b : $op eq 'fmul' ? $a * $b : $a / $b;
                $x = unpack('f', pack('f', $x)) if $ty eq 'float';
                $const{$name} = '0x' . uc unpack('H16', pack('d>', $x));
                next;
            }
            # A pointer cast to a pointer is the pointer.
            if (/^\s+(%[-\w.\$]+) = bitcast ptr (%[-\w.\$]+|\@[-\w.\$]+) to ptr$/) {
                $const{$1} = $2;
                next;
            }
            next unless /^\s+(%[-\w.\$]+) = (trunc|sext|zext) i(\d+) (-?\d+) to i(\d+)$/;
            my ($name, $op, $to, $c) = ($1, $2, $5, $4);
            next if $op eq 'zext' && $c < 0;
            next if $to < 64 && ($c >= 2 ** ($to - 1) || $c < -(2 ** ($to - 1)));
            $const{$name} = $c;
        }
        return @lines unless %const;
        my @out;
        for my $line (@lines) {
            next if $line =~ /^\s+(%[-\w.\$]+) = / && exists $const{$1};
            $line =~ s/(?<![-\w.\$])(%[-\w.\$]+)(?![-\w.\$])/exists $const{$1} ? $const{$1} : $1/ge;
            push @out, $line;
        }
        @lines = @out;
    }
}

# Where a fixed-size alloca sits among the entry block's others can't matter —
# they all run before anything uses them — so they go in the order the code
# first uses them.
sub order_allocas {
    my @lines = @_;
    my %first;
    for my $i (0 .. $#lines) {
        my $rest = $lines[$i];
        next if $rest =~ /^\s+%[-\w.\$]+ = alloca /;
        $rest =~ s/^\s+%[-\w.\$]+ = //;
        while ($rest =~ /(%[-\w.\$]+)/g) { $first{$1} //= $i; }
    }
    # The entry block's allocas, and each other block's leading run of them
    # (hoisted there: @main's follow the program's setup).
    my (@runs, @at);
    my $entry = 1;
    for my $i (0 .. $#lines) {
        if ($i > 0 && $lines[$i] =~ /^[-\w.\$]+:/) { push @runs, [@at]; @at = (); $entry = 0; next }
        my $fixed = $lines[$i] =~ /^\s+%[-\w.\$]+ = alloca / && $lines[$i] !~ /, i\d+ %/;
        if ($fixed && ($entry || !@at || $at[-1] == $i - 1) && ($entry || $lines[$i - 1] =~ /^[-\w.\$]+:/ || @at)) { push @at, $i }
    }
    push @runs, [@at];
    for my $run (@runs) {
        my @at = @$run;
        next if @at < 2;
        my %name = map { $_ => ($lines[$_] =~ /^\s+(%[-\w.\$]+) = /)[0] } @at;
        my @order = sort {
            ($first{$name{$a}} // 1e9) <=> ($first{$name{$b}} // 1e9) || $a <=> $b
        } @at;
        @lines[@at] = @lines[@order];
    }
    return @lines;
}

# An alloca nothing reads — only stored into — is dead, and so are its stores;
# a load nothing uses (a load does nothing but produce its value).
sub drop_unread {
    my @lines = @_;
    my (%slot, %other, %used);
    for (@lines) {
        (my $line = $_) =~ s/^\s+%[-\w.\$]+ = //;
        $used{$1} = 1 while $line =~ /(%[-\w.\$]+)/g;
    }
    for (@lines) {
        $slot{$1} = 1 if /^\s+(%[-\w.\$]+) = alloca /;
    }
    for (@lines) {
        next if /^\s+%[-\w.\$]+ = alloca /;
        my $line = $_;
        # A store's pointer operand isn't a read of the slot; its value is.
        my $ptr = $line =~ /^\s+store .+, ptr (%[-\w.\$]+)$/ ? $1 : "";
        $line =~ s/, ptr \Q$ptr\E$// if $ptr ne "";
        $other{$1} = 1 while $line =~ /(%[-\w.\$]+)/g;
    }
    return grep {
        !(/^\s+(%[-\w.\$]+) = alloca / && !$other{$1}) &&
        !(/^\s+store .+, ptr (%[-\w.\$]+)$/ && $slot{$1} && !$other{$1}) &&
        !(/^\s+(%[-\w.\$]+) = load / && !$used{$1})
    } @lines;
}

# Address arithmetic whose shape can't change behavior: `inbounds` dropped, a
# getelementptr nothing uses dropped, and one whose base is another's result
# folded into it (a chain of steps is one getelementptr; the base stays while
# something else uses it).
sub simplify_geps {
    my @lines = map {
        my $l = $_;
        chomp $l;
        $l =~ s/ = getelementptr inbounds / = getelementptr /;
        # The indices, after the base: a constant's width, i64.
        if ($l =~ /^(\s+%[-\w.\$]+ = getelementptr .*?, ptr [%@][-\w.\$]+)(.*)$/) {
            my ($head, $at) = ($1, $2);
            $at =~ s/\bi32 (-?\d+)\b/i64 $1/g;
            $l = $head . $at;
        }
        $l
    } @_;
    my $changed = 1;
    while ($changed) {
        $changed = 0;
        my (%uses, %def);
        for my $i (0 .. $#lines) {
            my $rest = $lines[$i];
            if ($rest =~ s/^\s+(%[-\w.\$]+) = //) { $def{$1} = $i; }
            $uses{$1}++ while $rest =~ /(%[-\w.\$]+)/g;
        }
        for my $i (0 .. $#lines) {
            my $line = $lines[$i];
            next unless defined $line;
            if ($line =~ /^\s+(%[-\w.\$]+) = getelementptr / && !$uses{$1}) {
                $lines[$i] = undef; $changed = 1; next;
            }
            next unless $line =~ /^(\s+%[-\w.\$]+ = getelementptr ).+?, ptr (%[-\w.\$]+), i(?:32|64) 0((?:, .*)?)$/;
            my ($head, $a, $rest) = ($1, $2, $3);
            next unless defined $def{$a};
            my $base = $lines[$def{$a}];
            next unless defined $base && $base =~ /^\s+\Q$a\E = getelementptr (.+)$/;
            $lines[$i] = $head . $1 . $rest;
            $changed = 1;
        }
        @lines = grep { defined } @lines;
    }
    return map { "$_\n" } sink_geps(@lines);
}

# Where a getelementptr is computed can't matter either — it touches no
# memory, and its operands dominate each of its uses — so each use (but a
# phi's) gets its own copy, just before it: one computed once and reused, and
# one computed again at each use, are the same.
sub sink_geps {
    my @lines = @_;
    my (%def, %phi);
    for my $i (0 .. $#lines) {
        $def{$1} = $i if $lines[$i] =~ /^\s+(%[-\w.\$]+) = getelementptr /;
        next unless $lines[$i] =~ / = phi /;
        $phi{$1} = 1 while $lines[$i] =~ /(%[-\w.\$]+)/g;
    }
    my %sink = map { $_ => 1 } grep { !$phi{$_} } keys %def;
    my (@out, %copies);
    my ($place, $copy);
    # A line, after copies of the getelementptrs it uses: each operand renamed
    # to its copy.
    $place = sub {
        my ($line) = @_;
        my ($head, $rest) = $line =~ /^(\s+%[-\w.\$]+ = )?(.*)$/s;
        $rest =~ s/(?<![-\w.\$])(%[-\w.\$]+)(?![-\w.\$])/$sink{$1} ? $copy->($1) : $1/ge;
        push @out, ($head // "") . $rest;
    };
    $copy = sub {
        my ($v) = @_;
        my $n = $copies{$v}++ ? "$v.copy$copies{$v}" : $v;
        my $gep = $lines[$def{$v}];
        $gep =~ s/^(\s+)\Q$v\E = /$1$n = /;
        $place->($gep);
        return $n;
    };
    for my $line (@lines) {
        next if $line =~ /^\s+(%[-\w.\$]+) = getelementptr / && $sink{$1};
        $place->($line);
    }
    return @out;
}

# A store the next store overwrites (same type, same pointer; only address
# arithmetic between) does nothing;
# nor does a zeroing memset the next line repeats, or overwrites with a memcpy
# of the same size; nor one of no more than the memset just before it zeroed
# at the same pointer (only address arithmetic between).
sub drop_overwritten {
    my @lines = @_;
    my @out;
    my ($zp, $zn) = ("", -1);   # what the last kept memset zeroed, while nothing since touched memory
    # A getelementptr's name → what it computes: the same text is the same
    # address. Known up front, since a later store's address may be computed
    # after this line.
    my %at;
    for (@lines) {
        $at{$1} = $2 if /^\s+(%[-\w.\$]+) = (getelementptr .*)$/;
    }
    my $where = sub { my ($p) = @_; return $at{$p} // $p };
    for my $i (0 .. $#lines) {
        if ($lines[$i] =~ /^\s+call void \@llvm\.memset\.p0\.i64\(ptr (%[-\w.\$]+), i8 0, i64 (\d+), i1 false\)$/ && $where->($1) eq $zp && $2 <= $zn) {
            next;
        }
        if ($lines[$i] !~ /^\s+%[-\w.\$]+ = getelementptr /) { ($zp, $zn) = ("", -1) }
        my $next = $i < $#lines ? $lines[$i + 1] : "";
        my ($t1, $p1) = store_of($lines[$i]);
        if (defined $t1) {
            # The next store, past address arithmetic (it touches no memory).
            my $j = $i + 1;
            $j++ while $j <= $#lines && $lines[$j] =~ /^\s+%[-\w.\$]+ = getelementptr /;
            my ($t2, $p2) = store_of($j <= $#lines ? $lines[$j] : "");
            next if defined $t2 && $t1 eq $t2 && $where->($p1) eq $where->($p2);
        }
        if ($lines[$i] =~ /^\s+call void \@llvm\.memset\.p0\.i64\(ptr (%[-\w.\$]+), i8 0, i64 (\d+), i1 false\)$/) {
            my ($p, $n) = ($1, $2);
            next if $next eq $lines[$i];
            # The memcpy may come after address arithmetic, which touches no memory.
            my $j = $i + 1;
            $j++ while $j <= $#lines && $lines[$j] =~ /^\s+%[-\w.\$]+ = getelementptr /;
            my $copy = $j <= $#lines ? $lines[$j] : "";
            next if $copy =~ /^\s+call void \@llvm\.memcpy\.p0\.p0\.i64\(ptr \Q$p\E, ptr [^,]+, i64 $n, i1 false\)$/;
            ($zp, $zn) = ($where->($p), $n);
        }
        push @out, $lines[$i];
    }
    return @out;
}

# A store's type and pointer: `store <type> <value>, ptr <pointer>`.
# A slot stored once, with a constant, where that store comes before each of
# its loads — earlier in the store's block, or in a block the store's block
# dominates — is that constant: its loads are the constant, and the slot and
# its store go. Only a slot nothing else touches (no call, copy or address
# arithmetic sees it).
sub forward_constants {
    my @lines = @_;
    my (%slot, %store, %loads, %bad);
    for (@lines) { $slot{$1} = 1 if /^\s+(%[-\w.\$]+) = alloca / }
    for my $i (0 .. $#lines) {
        local $_ = $lines[$i];
        next if /^\s+%[-\w.\$]+ = alloca /;
        if (/^\s+store (\S+) (\S+), ptr (%[-\w.\$]+)$/ && $slot{$3} && $2 !~ /%|undef|poison/) {
            $bad{$3} = 1 if $store{$3};
            $store{$3} = [$i, $1, $2];
            next;
        }
        if (/^\s+(%[-\w.\$]+) = load (\S+), ptr (%[-\w.\$]+)$/) {
            push @{ $loads{$3} }, [$i, $1, $2];
            next;
        }
        (my $line = $_) =~ s/^\s+%[-\w.\$]+ = //;
        $bad{$1} = 1 while $line =~ /(%[-\w.\$]+)/g;
    }
    my @slots = grep { !$bad{$_} } keys %store;
    return @lines unless @slots;

    # Blocks (the entry and each label's) and their successors.
    my (@block, %index, @succ);
    my $b = 0;
    for my $i (0 .. $#lines) {
        $b++ if $i > 0 && $lines[$i] =~ /^[-\w.\$]+:/;
        $index{$1} = $b if $lines[$i] =~ /^([-\w.\$]+):/;
        $block[$i] = $b;
    }
    for my $i (0 .. $#lines) {
        next unless $lines[$i] =~ /^\s+(br|switch|i\d+ -?\d+, label)\b/;
        while ($lines[$i] =~ /label %([-\w.\$]+)/g) {
            push @{ $succ[$block[$i]] }, $index{$1} if defined $index{$1};
        }
    }
    # The blocks the entry reaches without passing through block $d: the ones
    # $d doesn't dominate.
    my %around;
    my $reached = sub {
        my ($d) = @_;
        return $around{$d} //= do {
            my %seen;
            my @todo = $d == 0 ? () : (0);
            $seen{0} = 1 if @todo;
            while (@todo) {
                for my $s (@{ $succ[pop @todo] // [] }) {
                    next if $s == $d || $seen{$s}++;
                    push @todo, $s;
                }
            }
            \%seen;
        };
    };

    my (%value, %drop);
    for my $s (@slots) {
        my ($at, $type, $c) = @{ $store{$s} };
        my $sb = $block[$at];
        my $ok = 1;
        for my $l (@{ $loads{$s} // [] }) {
            my ($li, undef, $lt) = @$l;
            $ok = 0 if $lt ne $type;
            $ok = 0 if $block[$li] == $sb ? $li < $at : $reached->($sb)->{$block[$li]};
        }
        next unless $ok;
        $drop{$at} = 1;
        for my $l (@{ $loads{$s} // [] }) { $drop{$l->[0]} = 1; $value{$l->[1]} = $c }
    }
    return @lines unless %drop;
    my @out;
    for my $i (0 .. $#lines) {
        next if $drop{$i};
        (my $line = $lines[$i]) =~ s/(%[-\w.\$]+)/$value{$1} \/\/ $1/ge;
        push @out, $line;
    }
    return @out;   # (the slot itself: drop_unread, nothing reads it now)
}

sub store_of {
    my ($line) = @_;
    return unless $line =~ /^\s+store (.+) (\S+), ptr (%[-\w.\$]+)$/;
    return ($1, $3);
}
