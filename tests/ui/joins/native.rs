//@ run-pass
#![feature(joins)]
#![allow(incomplete_features)]

// Keep this compiler-suite fixture self-contained. The real prototype links
// `joins-runtime`; this small stand-in lets rustc's own UI harness exercise
// parsing, built-in expansion, visibility, and ordinary type checking without
// adding a cross-repository test dependency.
extern crate self as joins_runtime;

pub struct Reply<T>(std::marker::PhantomData<T>);

#[derive(Clone)]
pub struct JoinError;

pub struct QueryScope;

pub struct SourceLocation;

pub fn source_location(_file: &str, _line: u32, _column: u32) -> SourceLocation {
    SourceLocation
}

pub fn block_on<F: std::future::Future>(_: F) -> F::Output {
    panic!("self-contained compiler fixture does not execute async reactions")
}

pub struct PairMatcher<L, R, LO, RO>(std::marker::PhantomData<(L, R, LO, RO)>);

impl<L, R, LO, RO> Clone for PairMatcher<L, R, LO, RO> {
    fn clone(&self) -> Self {
        Self(std::marker::PhantomData)
    }
}

impl<L, R, LO, RO> PairMatcher<L, R, LO, RO> {
    pub fn new() -> Self {
        Self(std::marker::PhantomData)
    }

    pub fn new_in_scope(_scope: QueryScope) -> Self {
        Self(std::marker::PhantomData)
    }

    pub fn submit_left(&self, _value: L) -> Reply<LO> {
        Reply(std::marker::PhantomData)
    }

    pub fn submit_left_at(&self, _value: L, _source: SourceLocation) -> Reply<LO> {
        Reply(std::marker::PhantomData)
    }

    pub fn submit_right(&self, _value: R) -> Reply<RO> {
        Reply(std::marker::PhantomData)
    }

    pub fn submit_right_at(&self, _value: R, _source: SourceLocation) -> Reply<RO> {
        Reply(std::marker::PhantomData)
    }

    pub fn __join_dispatch_once<F>(&self, _body: F) -> bool
    where
        F: FnOnce(L, R) -> (Result<LO, JoinError>, Result<RO, JoinError>),
    {
        false
    }

    pub fn __join_dispatch_once_at<F>(&self, _source: SourceLocation, _body: F) -> bool
    where
        F: FnOnce(L, R) -> (Result<LO, JoinError>, Result<RO, JoinError>),
    {
        false
    }
}

join impl Native {
    channel left(value: u32) -> u32;
    channel right(value: u32) -> u32;

    when left(left) & right(right) {
        return { left: left + right, right: left + right };
    }
}

join impl AsyncNative {
    channel left(value: u32) -> u32;
    channel right(value: u32) -> u32;

    async when left(left) & right(right) {
        let sum = async { left + right }.await;
        return { left: sum, right: sum };
    }
}

fn main() {
    let endpoint = Native::new();
    let _scoped = Native::new_in_scope(QueryScope);
    let _left = endpoint.left(1);
    let _right = endpoint.right(2);
}
