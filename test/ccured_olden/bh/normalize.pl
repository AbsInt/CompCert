#!/usr/bin/perl -w
# strip wallclock times from output so we can compare

while ($line = <STDIN>) {
  # I don't know if it's a problem, but we seem to get some difference
  # about whether the 0's are positive or negative.. so let's change
  # all occurrances of "-0.0000" to simply " 0.0000"
  $line =~ s/-0\.0000/ 0.0000/g;

  ($firstSix) = ($line =~ /^(\s+\S+\s+\S+\s+\S+\s+\S+\s+\S+\s+\S+)\s+\S+$/);
  if ($firstSix) {
    # only output the first 6 columns
    print ("$firstSix\n");
  }
  else {
    # no match; print whole line
    print ($line);
  }
}
