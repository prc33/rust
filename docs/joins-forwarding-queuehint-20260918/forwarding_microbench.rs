#![feature(joins)]
extern crate joins_runtime;

use std::{future::Future, hint::black_box, task::{Context, Poll, Waker}, time::Instant};

// Compiled only into a separate diagnostic binary; absent from timed runs.
#[cfg(allocation_probe)]
mod allocations {
    use std::{alloc::{GlobalAlloc, Layout, System}, sync::atomic::{AtomicU64, Ordering}};
    pub static COUNT: AtomicU64 = AtomicU64::new(0);
    struct Counting;
    unsafe impl GlobalAlloc for Counting {
        unsafe fn alloc(&self, layout: Layout) -> *mut u8 {
            COUNT.fetch_add(1, Ordering::Relaxed);
            unsafe { System.alloc(layout) }
        }
        unsafe fn dealloc(&self, ptr: *mut u8, layout: Layout) {
            unsafe { System.dealloc(ptr, layout) }
        }
        unsafe fn alloc_zeroed(&self, layout: Layout) -> *mut u8 {
            COUNT.fetch_add(1, Ordering::Relaxed);
            unsafe { System.alloc_zeroed(layout) }
        }
        unsafe fn realloc(&self, ptr: *mut u8, layout: Layout, size: usize) -> *mut u8 {
            COUNT.fetch_add(1, Ordering::Relaxed);
            unsafe { System.realloc(ptr, layout, size) }
        }
    }
    #[global_allocator]
    static ALLOCATOR: Counting = Counting;
}

join impl Inner {
    channel step(value: u64) -> u64;
    channel unused();
    when step(value) {
        return { step: value.wrapping_add(1) };
    }
}

join impl Forward {
    channel run(value: u64) -> u64;
    async when run(value) {
        let inner = Inner::new();
        let reply = inner.step(value);
        let result = reply.await.unwrap();
        return { run: result.wrapping_mul(2) };
    }
}

join impl Unary {
    channel run(value: u64) -> u64;
    async when run(value) {
        return { run: value.wrapping_add(1).wrapping_mul(2) };
    }
}

async fn ordinary(value: u64) -> u64 {
    async { value.wrapping_add(1) }.await.wrapping_mul(2)
}

#[inline(always)]
fn finish(future: impl Future<Output = u64>) -> u64 {
    let mut future = std::pin::pin!(future);
    let mut cx = Context::from_waker(Waker::noop());
    match future.as_mut().poll(&mut cx) {
        Poll::Ready(value) => value,
        Poll::Pending => panic!("standalone synchronous forwarding unexpectedly suspended"),
    }
}

fn main() {
    let mut args = std::env::args().skip(1);
    let case = args.next().unwrap();
    let iterations: u64 = args.next().unwrap().parse().unwrap();
    #[cfg(allocation_probe)]
    let before = allocations::COUNT.load(std::sync::atomic::Ordering::Relaxed);
    let start = Instant::now();
    let mut checksum = 0u64;
    // Select outside the hot loop, without an indirect function call per op.
    macro_rules! measure {
        ($body:expr) => {
            for value in 0..iterations {
                let result = ($body)(black_box(value));
                checksum = black_box(checksum.wrapping_add(result));
            }
        };
    }
    match case.as_str() {
        "direct" => measure!(|value: u64| value.wrapping_add(1).wrapping_mul(2)),
        "async" => measure!(|value| finish(ordinary(value))),
        "unary" => measure!(|value| finish(Unary::new().run(value))),
        "forwarding" => measure!(|value| finish(Forward::new().run(value))),
        _ => panic!("unknown case"),
    }
    let elapsed = start.elapsed().as_nanos();
    assert_eq!(checksum, iterations.wrapping_mul(iterations.wrapping_add(1)));
    #[cfg(not(allocation_probe))]
    println!("{elapsed},{checksum}");
    #[cfg(allocation_probe)]
    {
        let count = allocations::COUNT.load(std::sync::atomic::Ordering::Relaxed) - before;
        println!("{elapsed},{checksum},{count}");
    }
}
