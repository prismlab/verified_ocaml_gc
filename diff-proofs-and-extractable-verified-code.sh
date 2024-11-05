#!/usr/bin/env sh

set -x

for file in $(ls Proofs/); do
 difft Proofs/$file  $(find ExtractableVerifiedCode -name $file)
done
