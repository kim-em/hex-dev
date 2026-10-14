# Counted-node field assessment

The compiler records all five fields of `Node.Counted`. They are part of the
existing structure assessment, not separate handwritten declarations. The
`counts` projection has no term references in this capture; its explicit
count contract is retained as a convenience for public consumers.

| Field | Reference clients | Disposition |
| --- | --- | --- |
| `basis` | 1 | Retain equality with the actual rank producer certificate for the retained matrix. |
| `checked` | 1 | Retain the independent node acceptance proof. |
| `counts` | 0 | Retain a direct exact-count projection for consumers; it follows from the other fields, so its zero term references are not a new mathematical invariant. |
| `cover` | 1 | Retain completeness of candidate support; matrix equations alone cannot discharge it. |
| `values` | 1 | Retain agreement of stored moments with the interpreted observation list. |
