#!/usr/bin/perl
# irnorm.pl — canonical form of a Mara .ll file, for comparing codegen output
# modulo naming: inside each function, locals and labels are renamed by order
# of first appearance (%v0, %v1, ...); string globals are replaced by their
# contents. Named types (%class.X = type ...) are left alone.
#
# Before renaming, each function drops what can't change what it does (phase 3
# compares two emitters, design/graph_retrofit.md), one rule each:
#   - a block no branch reaches from the entry;
#   - a store the next instruction overwrites: same type, same pointer (after
#     only address arithmetic);
#   - a constant's width changed, which is that constant at the new width;
#   - address arithmetic whose shape can't matter: `inbounds`, a constant
#     index's width (it is sign-extended to the pointer's: `i32 1` and
#     `i64 1` step alike), an unused getelementptr, a chain of them folded
#     into one, where one is computed (a copy just before each use);
#   - a zeroing memset the next instruction repeats, or overwrites with a
#     memcpy of the same size (after only address arithmetic); and one of no
#     more than the memset just before it zeroed at the same pointer;
#   - an alloca nothing reads (only stored into), with its stores;
#   - the order of the entry block's allocas (by first use);
#   - the name a bounds failure reports for the place it indexes: the graph's
#     emitter names it as written (`o.cells`, `grid[i]`), the old one by its
#     last name or as `array` (a message change, made on purpose);
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
    s/(call void \@__mara_bounds_fail\(.*, )ptr \@[-\w.\$]+\)$/${1}ptr NAME)/ for @kept;
    return order_allocas(simplify_geps(drop_overwritten(drop_unread(simplify_geps(fold_widths(@kept))))));   # (again: what a dropped memset addressed)
}

# A constant's width changed (`trunc i64 0 to i32`, `fptrunc double 0.5 to
# float`) is the constant itself at the new width, when it fits exactly: its
# uses take the constant.
sub fold_widths {
    my @lines = @_;
    my %const;
    for (@lines) {
        if (/^\s+(%[-\w.\$]+) = (fptrunc double|fpext float) (0x[0-9A-Fa-f]{16}) to (float|double)$/) {
            my ($name, $c) = ($1, $3);
            my $d = unpack('d>', pack('H16', substr($c, 2)));
            $const{$name} = $c if $2 eq 'fpext float' || unpack('f', pack('f', $d)) == $d;
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
    return @out;
}

# Where a fixed-size alloca sits among the entry block's others can't matter —
# they all run before anything uses them — so they go in the order the code
# first uses them.
sub order_allocas {
    my @lines = @_;
    my (@at, %first);
    for my $i (0 .. $#lines) {
        last if $i > 0 && $lines[$i] =~ /^[-\w.\$]+:/;   # the entry block only
        push @at, $i if $lines[$i] =~ /^\s+%[-\w.\$]+ = alloca / && $lines[$i] !~ /, i\d+ %/;
    }
    return @lines if @at < 2;
    for my $i (0 .. $#lines) {
        my $rest = $lines[$i];
        next if $rest =~ /^\s+%[-\w.\$]+ = alloca /;
        $rest =~ s/^\s+%[-\w.\$]+ = //;
        while ($rest =~ /(%[-\w.\$]+)/g) { $first{$1} //= $i; }
    }
    my %name = map { $_ => ($lines[$_] =~ /^\s+(%[-\w.\$]+) = /)[0] } @at;
    my @order = sort {
        ($first{$name{$a}} // 1e9) <=> ($first{$name{$b}} // 1e9) || $a <=> $b
    } @at;
    @lines[@at] = @lines[@order];
    return @lines;
}

# An alloca nothing reads — only stored into — is dead, and so are its stores.
sub drop_unread {
    my @lines = @_;
    my (%slot, %other);
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
        !(/^\s+store .+, ptr (%[-\w.\$]+)$/ && $slot{$1} && !$other{$1})
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
    my %at;                      # a getelementptr's name → what it computes (the same text: the same address)
    my $where = sub { my ($p) = @_; return $at{$p} // $p };
    for my $i (0 .. $#lines) {
        $at{$1} = $2 if $lines[$i] =~ /^\s+(%[-\w.\$]+) = (getelementptr .*)$/;
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
            next if defined $t2 && $t1 eq $t2 && $p1 eq $p2;
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
sub store_of {
    my ($line) = @_;
    return unless $line =~ /^\s+store (.+) (\S+), ptr (%[-\w.\$]+)$/;
    return ($1, $3);
}
