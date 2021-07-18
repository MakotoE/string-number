`StringNumber` is a decimal number type that stores the number as a string.

The "rules" that are followed for the implementation of `StringNumber` are:

- Only the string representation of the number may be stored, excluding local variables.
- For operations: no conversion from `StringNumber` to a different type. Only one digit of the number may be converted at a time.

As you might expect, the benchmark results are horrible compared to those of `f64`.

```
test f64_add ... bench:           0 ns/iter (+/- 0)
test f64_sub ... bench:           0 ns/iter (+/- 0)
test f64_mul ... bench:           0 ns/iter (+/- 0)
test string_add ... bench:         135 ns/iter (+/- 3)
test string_sub ... bench:         187 ns/iter (+/- 14)
test string_mul ... bench:         972 ns/iter (+/- 5)
```

But this doesn't mean that `StringNumber` is completely useless. Here are some reasons why you might want to use `StringNumber`:

```
// TODO think of a reason why anyone would want to use it
```
