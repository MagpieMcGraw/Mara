#!/usr/bin/perl
# irnorm.pl — canonical form of a Mara .ll file, for comparing codegen output
# modulo naming: inside each function, locals and labels are renamed by order
# of first appearance (%v0, %v1, ...); string globals are replaced by their
# contents. Named types (%class.X = type ...) are left alone.
#
# Before renaming, each function drops what can't change what it does (phase 3
# compares two emitters, design/graph_retrofit.md), one rule each:
#   - a block no branch reaches from the entry;
#   - a store the next instruction overwrites: same type, same pointer;
#   - then, a string constant nothing references.
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
        push @kept, drop_overwritten(@{ $blocks[$i]{lines} });
    }
    return @kept;
}

# A store the very next line overwrites (same type, same pointer) does nothing.
sub drop_overwritten {
    my @lines = @_;
    my @out;
    for my $i (0 .. $#lines) {
        my ($t1, $p1) = store_of($lines[$i]);
        if (defined $t1 && $i < $#lines) {
            my ($t2, $p2) = store_of($lines[$i + 1]);
            next if defined $t2 && $t1 eq $t2 && $p1 eq $p2;
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
