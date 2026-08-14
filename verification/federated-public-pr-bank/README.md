# Federated public pull-request Lean bank

This project materializes one SHA-deduplicated copy of every conservative,
UTF-8 Lean source blob found across fetched public `refs/pull/*/head` refs and
absent from the checked-out branch head. It then delegates to the established
`verification/unified-exhaustive-bank/generate_bank.py` compiler pipeline.

The generated theorem

```lean
UnifiedMillenniumPublicBank.acceptedCorpusKernelBundle
```

directly depends on every theorem constant in the maximal compatible imported
closure. The workflow requires at least 700 source-level theorem/lemma
occurrences and at least 700 imported kernel theorem constants before it can
succeed.

The extraction prefilter rejects proof holes, custom postulates,
`unsafe`/native/foreign escapes, file inclusion, and compile-time execution
commands. The downstream generator independently repeats its trust scan,
compiles files one by one, isolates aggregate collisions, and prints the final
axiom report.

This is a public-PR compatibility and provenance certificate. It is not a count
of distinct mathematical discoveries, does not cover inaccessible private
branches, and does not prove any open Clay Millennium problem.
