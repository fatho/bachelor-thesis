#!/bin/bash

GREEN="\e[32m"
NONE="\e[0m"

print_status()
{
  printf "$GREEN"
  printf "$1"
  printf "$NONE\n"
}

REBUILD=""
if [ "$1" == "rebuild" ]; then
 REBUILD="yes"
fi

SANDBOXDIR=`pwd`/.cabal-sandbox

print_status "cabal version: `cabal --version`"

if [ -n "$REBUILD" ]; then
  print_status "Rebuilding..."
  rm -r "$SANDBOXDIR"
  rm "cabal.sandbox.config"
fi
if [ ! -f cabal.sandbox.config ]; then
  print_status "Initializing sandbox"
  cabal sandbox init
fi

# install packages
packages=("dependencies/ba-funlogic-common/funlogic-core"
      "dependencies/ba-funlogic-common/language-cumin"
      "dependencies/ba-funlogic-common/language-salt"
      "code/haskeline-repl"
      "code/denotational-funlogic"
      "code/denotational-cumin"
      "code/denotational-salt")

printf "$GREEN"
print_status "Initializing packages..."
for dep in ${packages[@]}
do
  print_status "> initializing $dep"
  pushd "$dep"
  if [ -n "$REBUILD" ]; then
    rm "cabal.sandbox.config"
  fi
  if [ ! -f cabal.sandbox.config ]; then
    print_status "initializing sandbox"
    cabal sandbox init --sandbox="$SANDBOXDIR"
  fi
  # 1st constraint is needed since indentation defaults to parsec
  # 2nd constraint is needed since blaze-markup 0.6.3 breaks trifecta
  cabal install -j --only-dependencies \
    --constraint="indentation +trifecta -parsec" \
    --constraint "blaze-markup==0.6.2.0" \
    && cabal clean \
    && cabal configure \
    && cabal install
  popd
  cabal sandbox add-source "$dep"
done
