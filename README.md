# phobos-next

Various reusable D code.

Most definitions are probably generic enough to be part of Phobos.

See also: http://forum.dlang.org/post/tppptevxiygafzpicmgz@forum.dlang.org

It includes various kinds of

- Integer Sorting Algorithms, such as Non-In-Place Radix Sort: `intsort.d`
- Clever Printing of Groups of arrays/slices: `show.d`
- Boyer Moore Hoorspool Search: `horspool.d`
- Symbol Regex (Structured Regular Expressions similar to Elisps rx): `symbolic.d`
- extension to Phobos (often ending with _ex.d)
- A compile-time fixed-size variant of `bitarray.d` i call `bitset.d`
- An N-Gram implementation (many nested for loops): `ngram.d`
- A wrapper for bounded types: `bound.d`
- Computer Science Units: `csunits.d`
- Enhanced `NotNull`: `notnull.d`
- A structured wrapper for message digests: `digest_ex.d`
- a bunch of various D sample code starting with `t_` in `tests`.
- Open/LibreOffice file that includes various kinds of comments and suggestions for improvements to D's build process.
