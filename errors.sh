#!/bin/sh

set -x
set -e

cargo run --example errors
./plot.sh

exit 0
