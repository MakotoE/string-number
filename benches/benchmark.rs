use criterion::{black_box, criterion_group, criterion_main, Criterion};
use string_number::StringNumber;

criterion_group!(benches, benchmark);
criterion_main!(benches);

const A: f64 = 69.0;
const B: f64 = 420.0;

fn benchmark(c: &mut Criterion) {
    let a = black_box(A);
    let b = black_box(B);
    c.bench_function("f64_add", |be| be.iter(|| black_box(a + b)));
    c.bench_function("f64_sub", |be| be.iter(|| black_box(a - b)));
    c.bench_function("f64_mul", |be| be.iter(|| black_box(a * b)));

    let a: StringNumber = A.into();
    let b: StringNumber = b.into();
    c.bench_function("string_add", |be| {
        be.iter(|| black_box(a.clone() + b.clone()))
    });
    c.bench_function("string_sub", |be| {
        be.iter(|| black_box(a.clone() - b.clone()))
    });
    c.bench_function("string_mul", |be| {
        be.iter(|| black_box(a.clone() * b.clone()))
    });
}

/*
test f64_add ... bench:           0 ns/iter (+/- 0)

test f64_sub ... bench:           0 ns/iter (+/- 0)

test f64_mul ... bench:           0 ns/iter (+/- 0)

test string_add ... bench:         135 ns/iter (+/- 3)

test string_sub ... bench:         187 ns/iter (+/- 14)

test string_mul ... bench:         972 ns/iter (+/- 5)
 */
