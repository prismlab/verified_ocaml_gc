#!/usr/bin/env sh

set -x

for file in $(ls ./ExtractableVerifiedCode/dist/internal); do
    difft ./ExtractableVerifiedCode/dist/internal/$file  $(find ./ExtractedCodeIntegratedWithRuntime/ocaml-4.14-verified-gc/runtime/verified_gc/internal -name $file)
done


difft ./ExtractableVerifiedCode/dist/Spec.h ./ExtractedCodeIntegratedWithRuntime/ocaml-4.14-verified-gc/runtime/verified_gc/Spec.h
difft ./ExtractableVerifiedCode/dist/Spec.c ./ExtractedCodeIntegratedWithRuntime/ocaml-4.14-verified-gc/runtime/verified_gc/Spec.c
difft ./ExtractableVerifiedCode/dist/Impl_GC_closure_infix_ver3.h ./ExtractedCodeIntegratedWithRuntime/ocaml-4.14-verified-gc/runtime/verified_gc/Impl_GC_closure_infix_ver3.h
difft ./ExtractableVerifiedCode/dist/Impl_GC_closure_infix_ver3.c ./ExtractedCodeIntegratedWithRuntime/ocaml-4.14-verified-gc/runtime/verified_gc/Impl_GC_closure_infix_ver3.c
