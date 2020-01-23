#!/bin/sh

for file in *.csv; do
  name=$(basename -s .csv $file)
  echo "
    set terminal png
    set datafile separator \",\"
    set output \"$name.png\"
    plot '$file' using 1:2 with lines lt rgb \"blue\", \
      '$file' using 1:3 with lines lt rgb \"red\"
  " | gnuplot
done

exit 0
