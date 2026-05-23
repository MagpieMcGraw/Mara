#!/usr/bin/env perl
# Extract format strings from check_error/check_warning calls and
# replace them with named constants. Writes:
#   - tools/diagnostics_typecheck.txt  : NAME :: "format" lines for diagnostics.odin
#   - the modified <source>            : with constants in place of strings
#
# Usage: perl tools/extract_diagnostics.pl <source-file> <prefix>
#   <source-file>  : odin file to process (read+write)
#   <prefix>       : constant prefix, e.g. TYPE_, CODE_
#
# Idempotent within a single run; doesn't touch already-replaced sites.

use strict;
use warnings;

die "usage: $0 <prefix> <source-file>+\n" unless @ARGV >= 2;
my $prefix = shift @ARGV;
my @src_files = @ARGV;

# Read all sources (concatenated, with per-file index for write-back)
my @file_text;
my $src = "";
for my $f (@src_files) {
    open my $fh, '<', $f or die "open $f: $!";
    local $/;
    my $text = <$fh>;
    push @file_text, $text;
    $src .= $text;
}

# Pattern: helper(arg, span, "format string", ...).
# The format string is captured WITH its outer quotes — that's the literal
# we'll replace at call sites later. The string body allows Odin-style
# escapes (\\.) and any non-special char.
my $call_re = qr/\b(?:check_error|check_warning|codegen_fatal)\(\s*\w+\s*,\s*[^,]+?\s*,\s*("(?:\\.|[^"\\])*")/;

# Collect unique format strings in first-seen order
my @unique;
my %seen;
my @matches = $src =~ /$call_re/g;
for my $fmt (@matches) {
    next if $seen{$fmt}++;
    push @unique, $fmt;
}

# Stopwords used in name generation
my %stop = map { $_ => 1 } qw(
    the a an is are of in on to for at by with but or and
    must can may has have does do this that these those it
    be been being its their there what which when where why how
    not no nor so yet because if then else as from will would
    you me they them their us we i he she him her got
);

# Generate a constant name for a format string
my %used_names;
sub make_name {
    my $fmt = shift;
    my $core = $fmt;
    # strip outer quotes
    $core =~ s/^"|"$//g;
    # turn escapes into spaces
    $core =~ s/\\[ntrabfv\\"\']/ /g;
    # drop printf specifiers
    $core =~ s/%[\#\+\-0-9.]*[svdcouxeEfgG%]/ /g;
    # punctuation -> space
    $core =~ s/[^A-Za-z0-9]/ /g;
    # tokenize
    my @words = grep { length($_) > 1 && !$stop{lc $_} } split /\s+/, $core;
    # cap at 5 words
    @words = @words[0 .. ($#words > 4 ? 4 : $#words)] if @words;
    @words = ('UNNAMED') unless @words;
    # uppercase, join
    my $base = $prefix . uc(join('_', @words));
    $base =~ s/_+/_/g;
    $base =~ s/_$//;
    my $name = $base;
    my $i = 2;
    while ($used_names{$name}) {
        $name = "${base}_${i}";
        $i++;
    }
    $used_names{$name} = 1;
    return $name;
}

# Build (name, fmt) pairs
my @pairs;
my %fmt_to_name;
for my $fmt (@unique) {
    my $name = make_name($fmt);
    push @pairs, [$name, $fmt];
    $fmt_to_name{$fmt} = $name;
}

# Apply replacements per file. Each fmt is a unique string literal, so
# simple literal replacement is safe within each file. We re-process the
# original per-file text so write-back lines up with the original file.
for my $i (0 .. $#src_files) {
    my $text = $file_text[$i];
    for my $fmt (@unique) {
        my $name = $fmt_to_name{$fmt};
        $text =~ s/\Q$fmt\E/$name/g;
    }
    open my $out, '>', $src_files[$i] or die "write $src_files[$i]: $!";
    print $out $text;
    close $out;
}

# Write constants file
my $name_part = lc $prefix;
$name_part =~ s/_$//;
my $const_file = "tools/diagnostics_${name_part}.txt";
open my $cf, '>', $const_file or die "write $const_file: $!";
for my $pair (@pairs) {
    my ($name, $fmt) = @$pair;
    print $cf "$name :: $fmt\n";
}
close $cf;

printf STDERR "Wrote %d constants to %s\n", scalar(@pairs), $const_file;
