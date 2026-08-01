#!/usr/bin/env perl
use strict;
use warnings;

# Enforce the checked-in Ix.Tc verification sorry frontier.
#
# This is a source-token audit rather than a raw grep: comments and strings
# may discuss upstream sorries without enlarging the local trusted frontier.
# Every real Lean sorry token is attributed to its nearest top-level
# declaration and compared with the exact allowlist below.

use Cwd qw(abs_path);
use FindBin qw($RealBin);
use File::Find qw(find);
use File::Spec;

my $repo_root = abs_path(File::Spec->catdir($RealBin, '..', '..'));
my $verify_root = File::Spec->catdir($repo_root, 'Ix', 'Tc', 'Verify');

my %expected = ();

sub mask_chunk {
  my ($chunk) = @_;
  $chunk =~ s/[^\n]/ /g;
  return $chunk;
}

sub earliest {
  my @positions = grep { $_ >= 0 } @_;
  return -1 unless @positions;
  my ($first) = sort { $a <=> $b } @positions;
  return $first;
}

sub mask_non_code {
  my ($source, $path) = @_;
  my $length = length $source;
  my $index = 0;
  my $block_depth = 0;
  my @masked;

  while ($index < $length) {
    if ($block_depth) {
      my $open = index($source, '/-', $index);
      my $close = index($source, '-/', $index);
      my $next = earliest($open, $close);
      die "$path: unterminated block comment\n" if $next < 0;
      push @masked, mask_chunk(substr($source, $index, $next + 2 - $index));
      if ($next == $open) {
        ++$block_depth;
      } else {
        --$block_depth;
      }
      $index = $next + 2;
      next;
    }

    my $line_comment = index($source, '--', $index);
    my $block_comment = index($source, '/-', $index);
    my $quote = index($source, '"', $index);
    my $next = earliest($line_comment, $block_comment, $quote);

    if ($next < 0) {
      push @masked, substr($source, $index);
      $index = $length;
      next;
    }

    push @masked, substr($source, $index, $next - $index);
    if ($next == $line_comment) {
      my $newline = index($source, "\n", $next);
      my $end = $newline < 0 ? $length : $newline;
      push @masked, mask_chunk(substr($source, $next, $end - $next));
      $index = $end;
    } elsif ($next == $block_comment) {
      push @masked, '  ';
      $block_depth = 1;
      $index = $next + 2;
    } else {
      my $closing = $next + 1;
      while (1) {
        $closing = index($source, '"', $closing);
        die "$path: unterminated string literal\n" if $closing < 0;
        my $slashes = 0;
        my $before = $closing - 1;
        while ($before > $next && substr($source, $before, 1) eq '\\') {
          ++$slashes;
          --$before;
        }
        last if $slashes % 2 == 0;
        ++$closing;
      }
      push @masked,
        mask_chunk(substr($source, $next, $closing + 1 - $next));
      $index = $closing + 1;
    }
  }

  die "$path: unterminated block comment\n" if $block_depth;
  return join '', @masked;
}

sub relative_path {
  my ($path) = @_;
  my $relative = File::Spec->abs2rel($path, $repo_root);
  $relative =~ s{\\}{/}g;
  return $relative;
}

sub find_sorries {
  my ($path) = @_;
  open my $handle, '<:encoding(UTF-8)', $path
    or die "cannot read $path: $!\n";
  local $/;
  my $source = <$handle>;
  close $handle;

  return () unless $source =~ /\bsorry\b/;
  my $code = mask_non_code($source, $path);
  my @commands;
  while (
    $code =~
      m{^[ \t]*(?:(?:private|protected|noncomputable)[ \t]+)*
        (theorem|lemma|def|opaque|abbrev|instance|inductive|structure|example)
        [ \t]+([A-Za-z_][A-Za-z0-9_'.?]*)}mgx
  ) {
    push @commands, [$-[0], $1, $2];
  }

  my @found;
  my $command_index = -1;
  while ($code =~ /\bsorry\b/g) {
    my $position = $-[0];
    while (
      $command_index + 1 < @commands
      && $commands[$command_index + 1]->[0] < $position
    ) {
      ++$command_index;
    }

    my $declaration = '<no enclosing declaration>';
    if ($command_index >= 0) {
      my ($unused, $kind, $name) = @{$commands[$command_index]};
      $declaration = $kind =~ /^(?:theorem|lemma)$/ ? $name : "$kind $name";
    }
    my $prefix = substr($source, 0, $position);
    my $line = 1 + ($prefix =~ tr/\n//);
    push @found, [relative_path($path), $declaration, $line];
  }
  return @found;
}

my @observed_with_lines;
eval {
  my @verify_files;
  find(
    {
      no_chdir => 1,
      wanted => sub {
        push @verify_files, $File::Find::name
          if -f $File::Find::name && $File::Find::name =~ /\.lean\z/;
      },
    },
    $verify_root,
  );
  for my $path (sort @verify_files) {
    push @observed_with_lines, find_sorries($path);
  }
  1;
} or do {
  my $error = $@ || 'unknown scan error';
  print STDERR "tc-verify sorry audit failed to scan sources: $error";
  exit 2;
};

my %observed;
for my $entry (@observed_with_lines) {
  ++$observed{"$entry->[0]\0$entry->[1]"};
}

my $matches = 1;
for my $key (keys %expected) {
  $matches = 0 if ($observed{$key} // 0) != $expected{$key};
}
for my $key (keys %observed) {
  $matches = 0 if ($expected{$key} // 0) != $observed{$key};
}

if (!$matches) {
  print STDERR "Ix.Tc Verify sorry frontier changed.\n";
  print STDERR "Expected:\n";
  for my $key (sort keys %expected) {
    my ($path, $declaration) = split /\0/, $key, 2;
    print STDERR "  $expected{$key} x $path :: $declaration\n";
  }
  print STDERR "Observed:\n";
  if (@observed_with_lines) {
    for my $entry (@observed_with_lines) {
      print STDERR "  $entry->[0]:$entry->[2] :: $entry->[1]\n";
    }
  } else {
    print STDERR "  <none>\n";
  }
  print STDERR
    "Update the allowlist only when the formal trust frontier intentionally changes.\n";
  exit 1;
}

print "Ix.Tc Verify sorry frontier OK:\n";
for my $entry (@observed_with_lines) {
  print "  $entry->[0]:$entry->[2] :: $entry->[1]\n";
}
