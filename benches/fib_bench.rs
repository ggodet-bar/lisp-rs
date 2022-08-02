use criterion::{black_box, criterion_group, criterion_main, Criterion};

#[path = "../src/lisprs/mod.rs"]
mod lisprs;

fn fibonacci(program: usize, env: &mut lisprs::LispEnv) {
    env.evaluate(program).unwrap();
}

fn criterion_benchmark(c: &mut Criterion) {
    // returns the nth item in the Fibonacci sequence
    for i in [5, 10, 20, 30] {
        c.bench_function(&format!("fib {}", i), |b| {
            b.iter(|| {
                let mut env = lisprs::LispEnv::new();
                let program = env
                    .parse(&format!(
                        r#"
    (def fib (N)
    	(if (<= N 1) N (+ (fib (- N 1)) (fib (- N 2)))))
    (fib {})"#,
                        i
                    ))
                    .unwrap();
                fibonacci(black_box(program), &mut env)
            })
        });
    }
}

criterion_group!(benches, criterion_benchmark);
criterion_main!(benches);
