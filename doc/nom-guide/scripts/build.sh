#!/bin/bash
command="build"

[[ "$1" == "serve" ]] && command="serve"

BOOK_ROOT_PATH="$( cd "$(dirname "$0")" >/dev/null 2>&1 ; pwd -P )/.."
cd $BOOK_ROOT_PATH

[[ ! -e $BOOK_ROOT_PATH/../../target ]] && (cd ../../ && cargo build)
mdbook test -L $(cd ../../ && pwd)/target/debug/deps/
mdbook $command
