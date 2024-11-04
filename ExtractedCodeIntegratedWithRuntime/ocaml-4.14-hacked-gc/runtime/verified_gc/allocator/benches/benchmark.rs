use criterion::{black_box, criterion_group, criterion_main, Criterion};
use rand::rngs::mock::StepRng;
use rand::rngs::SmallRng;
use rand::{Rng, SeedableRng};
use shuffle::fy::FisherYates;
use shuffle::shuffler::Shuffler;

fn _fragment_memory() {
    let mut rng = SmallRng::seed_from_u64(42);
    let mut rng1 = SmallRng::seed_from_u64(0xcafebabe);
    let h = 20000;

    let mut prev: *mut u8 = std::ptr::null_mut();
    (0..h).into_iter().for_each(|x| {
        let m = rust_allocator::alloc(rng.gen_range(1..100));
        if x != 0 && rng1.gen_range(1..=100) > 80 {
            rust_allocator::dealloc(prev);
        }
        prev = m;
    });
}

fn alloc_benchmark_small_inp(c: &mut Criterion) {
    // std::env::set_var("MIN_EXPANSION_WORDSIZE", "1048576");

    _fragment_memory();
    // println!("INFO: Fragmented memory");
    let mut rng1 = SmallRng::seed_from_u64(42);

    let mut vec = vec![];

    let mut step_rng = StepRng::new(2, 1);
    let mut fy = FisherYates::default();
    c.bench_function("alloc after some random fragmentation", |b| {
        b.iter(|| {
            let mem = rust_allocator::alloc(black_box(rng1.gen_range(1..=4096)));
            vec.push(mem);

            if vec.len() == 1000 {
                let _ = fy.shuffle(&mut vec, &mut step_rng);
                for i in 0..100 {
                    let entry = *vec.get_mut(i).unwrap();
                    let v = val_bp(entry);
                }
            }
        })
    });
}

criterion_group!(benches, alloc_benchmark_small_inp);
criterion_main!(benches);
