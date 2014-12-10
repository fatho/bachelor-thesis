#!/bin/bash

GREEN="\e[32m"
NONE="\e[0m"

print_status()
{
  printf "$GREEN"
  printf "$1"
  printf "$NONE\n"
}

if [ ! -f cabal.sandbox.config ]; then
  print_status "Initializing sandbox"
  cabal sandbox init
fi

# install dependencies
deps=("dependencies/ba-funlogic-common/funlogic-core"
      "dependencies/ba-funlogic-common/language-cumin"
      "dependencies/ba-funlogic-common/language-salt"
      "code/denotational-funlogic")

printf "$GREEN"
print_status "Installing dependencies..."
for dep in ${deps[@]}
do
  print_status "> installing $dep"
  pushd "$dep"
  cabal install -j --only-dependencies --constraint="indentation +trifecta -parsec" \
    && cabal configure \
    && cabal build \
    && cabal install
  popd
done