#![feature(test)]

extern crate gcd;

extern crate test;

use gcd::Gcd;


fn swap_sequence<T>(s: &mut [T], a: usize, b: usize, k: usize) {
    for i in 0..k {
        s.swap(a + i, b + i)
    }
}

fn swap_unchecked<T>(s: &mut [T], a: usize, b: usize, k: usize) {
    debug_assert!(a + k <= s.len());
    debug_assert!(b + k <= s.len());
    debug_assert!((a + k <= b) || (b + k <= a));
    for i in 0..k {
        unsafe {
            let pa: *mut T = s.get_unchecked_mut(a + i);
            let pb: *mut T = s.get_unchecked_mut(b + i);
            std::ptr::swap(pa, pb);
        }
    }
}

#[inline]
fn swap_inline<T>(s: &mut [T], k: usize) {
    // Swap front k items of sequence with back k items
    debug_assert!(k <= s.len() / 2);
    let b = s.len() - k;
    for i in 0..k {
        unsafe {
            let pa: *mut T = s.get_unchecked_mut(i);
            let pb: *mut T = s.get_unchecked_mut(b + i);
            std::ptr::swap(pa, pb);
        }
    }
}

#[inline]
fn addmod<T>(a: T, b: T, n: T) -> T
    where
        T: std::ops::Add<Output=T> + std::ops::Sub<Output=T> + Copy + PartialOrd
{
    // Faster than using the % operator, addition of two mod values can
    // never be more than 2n - 2, so a single subtraction gets back into range
    let c = a + b;
    if c >= n {
        c - n
    }
    else {
        c
    }
}

#[inline]
fn addmod_no_overflow<T>(a: T, b: T, n: T) -> T
    where
        T: std::ops::Add<Output=T> + std::ops::Sub<Output=T> + Copy + PartialOrd
{
    // Faster than using the % operator
    let c = n - a;
    if b >= c {
        // b >= n - a  ->  b + a >= n.
        // a < n, b < n  ->  a + b < 2n
        // Hence: n <= a + b <= 2n - 1  ->  0 < a + b - n < n - 1
        // a + b - n  =  b - n + a  =  b - (n - a)  =  b - c
        b - c
    }
    else {
        // if b < n - a, then b + a < n, and in the modulo range
        a + b
    }
}

fn rotate_adapt_gcd<T>(s: &mut [T], k: usize) {
    let n = s.len();
    if k == 0 || k == n {
        return
    }
    debug_assert!(k < n);
    match k.gcd(n - k) {
        1 => {
            let mut j = k;
            while j != 0 {
                s.swap(0, j);
                j = addmod(j, k, n);
            }
        },
        2 => {
            let mut j = k;
            while j != 0 {
                s.swap(0, j);
                s.swap(1, j + 1);
                j = addmod(j, k, n);
            }

        },
        blksize => {
            let mut j = k;
            for _ in 0 .. n / blksize - 1 {
                swap_inline(&mut s[0 .. j + blksize], blksize);
                j = addmod(j, k, n);
            }
        },
    }
}

fn rotate_adapt_gcd_no_overflow<T>(s: &mut [T], k: usize) {
    let n = s.len();
    if k == 0 || k == n {
        return
    }
    debug_assert!(k < n);
    match k.gcd(n - k) {
        1 => {
            let mut j = k;
            while j != 0 {
                s.swap(0, j);
                j = addmod_no_overflow(j, k, n);
            }
        },
        2 => {
            let mut j = k;
            while j != 0 {
                s.swap(0, j);
                s.swap(1, j + 1);
                j = addmod_no_overflow(j, k, n);
            }

        },
        blksize => {
            let mut j = k;
            for _ in 0 .. n / blksize - 1 {
                swap_inline(&mut s[0 .. j + blksize], blksize);
                j = addmod_no_overflow(j, k, n);
            }
        },
    }
}

fn rotate_adapt_gcd_unsafe<T>(s: &mut [T], k: usize) {
    let n = s.len();
    if k == 0 || k == n {
        return
    }
    debug_assert!(k < n);
    match k.gcd(n - k) {
        1 => {
            let mut j = k;
            while j != 0 {
                unsafe {
                    let pa: *mut T = s.get_unchecked_mut(0);
                    let pb: *mut T = s.get_unchecked_mut(j);
                    std::ptr::swap(pa, pb);
                }
                j = addmod(j, k, n);
            }
        },
        2 => {
            let mut j = k;
            while j != 0 {
                unsafe {
                    let pa: *mut T = s.get_unchecked_mut(0);
                    let pb: *mut T = s.get_unchecked_mut(1);
                    let pc: *mut T = s.get_unchecked_mut(j);
                    let pd: *mut T = s.get_unchecked_mut(j + 1);
                    std::ptr::swap(pa, pc);
                    std::ptr::swap(pb, pd);
                }
                s.swap(0, j);
                s.swap(1, j + 1);
                j = addmod(j, k, n);
            }

        },
        blksize => {
            let mut j = k;
            for _ in 0 .. n / blksize - 1 {
                swap_inline(&mut s[0 .. j + blksize], blksize);
                j = addmod(j, k, n);
            }
        },
    }
}

fn rotate_stride<T>(s: &mut [T], k: usize) {
    let n = s.len();
    if k == 0 || k == n {
        return
    }
    debug_assert!(n > k);
    let c = k.gcd(n - k);
    for i in 0 .. c {
        let mut j = (i + k) % n;
        while j != i {
            s.swap(i, j);
            j = (j + k) % n;
        }
    }
}

fn rotate_stride_addmod<T>(s: &mut [T], k: usize) {
    let n = s.len();
    if k == 0 || k == n {
        return
    }
    debug_assert!(n > k);
    let c = k.gcd(n - k);
    for i in 0 .. c {
        let mut j = addmod(i, k, n);
        while j != i {
            s.swap(i, j);
            j = addmod(j, k, n);
        }
    }
}

fn rotate_stride_unchecked<T>(s: &mut [T], k: usize) {
    let n = s.len();
    if k == 0 || k == n {
        return
    }
    debug_assert!(n > k);
    let c = k.gcd(n - k);
    for i in 0 .. c {
        let mut j = addmod(i, k, n);
        while j != i {
            unsafe {
                let pa: *mut T = s.get_unchecked_mut(i);
                let pb: *mut T = s.get_unchecked_mut(j);
                std::ptr::swap(pa, pb);
            }
            j = addmod(j, k, n);
        }
    }
}

fn rotate_block<T>(s: &mut [T], k: usize) {
    let n = s.len();
    if k == 0 || k == n {
        return
    }
    debug_assert!(n > k);
    let c = k.gcd(n - k);
    let mut p = k;
    for _ in 0 .. n / c - 1 {
        for i in 0..c {
            s.swap(i, p + i)
        }
        // swap_sequence(s, 0, p, c);
        p += k;
        if p > n { p -= n }
    }
}

fn rotate_block_addmod<T>(s: &mut [T], k: usize) {
    let n = s.len();
    if k == 0 || k == n {
        return
    }
    debug_assert!(n > k);
    let c = k.gcd(n - k);
    let mut p = k;
    for _ in 0 .. n / c - 1 {
        for i in 0..c {
            s.swap(i, p + i)
        }
        p = addmod(p, k, n);
    }
}

fn rotate_block_swap<T>(s: &mut [T], k: usize) {
    let n = s.len();
    if k == 0 || k == n {
        return
    }
    debug_assert!(n > k);
    let c = k.gcd(n - k);
    let mut p = k;
    for _ in 0 .. n / c - 1 {
        swap_unchecked(s, 0, p, c);
        p += k;
        if p >= n { p -= n }
    }
}

fn rotate_block_adapt<T>(s: &mut [T], k: usize) {
    let n = s.len();
    if k == 0 || k == n {
        return
    }
    debug_assert!(n > k);
    let c = k.gcd(n - k);
    if c == 1 {
        let mut j = k;
        while j != 0 {
            s.swap(0, j);
            j += k;
            if j >= n { j -= n }
        }
    } else {
        let mut j = k;
        for _ in 0 .. n / c - 1 {
            swap_unchecked(s, 0, j, c);
            j += k;
            if j >= n { j -= n }
        }
    }
}

fn rotate_block_unchecked<T>(s: &mut [T], k: usize) {
    let n = s.len();
    if k == 0 || k == n {
        return
    }
    debug_assert!(n > k);
    let c = k.gcd(n - k);
    let mut p = k;
    for _ in 0 .. n / c - 1 {
        for i in 0..c {
            unsafe {
                let pa: *mut T = s.get_unchecked_mut(i);
                let pb: *mut T = s.get_unchecked_mut(p + i);
                std::ptr::swap(pa, pb);
            }
        }
        p += k;
        if p >= n { p -= n }
    }
}

fn rotate_block_unchecked_addmod<T>(s: &mut [T], k: usize) {
    let n = s.len();
    if k == 0 || k == n {
        return
    }
    debug_assert!(n > k);
    let c = k.gcd(n - k);
    let mut p = k;
    for _ in 0 .. n / c - 1 {
        for i in 0..c {
            unsafe {
                let pa: *mut T = s.get_unchecked_mut(i);
                let pb: *mut T = s.get_unchecked_mut(p + i);
                std::ptr::swap(pa, pb);
            }
        }
        p = addmod(p, k, n);
    }
}

#[cfg(not(test))]
fn main() {
    println!("Hello, world!");
}

#[cfg(test)]
mod tests {
    use test::Bencher;

    #[test]
    #[should_panic]
    fn addmod_overflow() {
        let max = u16::max_value();
        super::addmod(max - 1, max - 1, max);
    }

    #[test]
    fn addmod_no_overflow() {
        let max = u16::max_value();
        assert_eq!(super::addmod_no_overflow(max - 1, max - 1, max), max - 2);
    }

    macro_rules! swap_test {
        ($name:ident, $name0:ident, $name1:ident, $name2:ident, $name3:ident) => {
            #[test]
            fn $name0() {
                let mut buf = [1, 2, 3, 4, 5, 6];
                super::$name(&mut buf, 0, 3, 3);
                assert_eq!(buf, [4, 5, 6, 1, 2, 3]);
            }

            #[test]
            fn $name1() {
                let mut buf = [1, 2, 3, 4, 5, 6];
                super::$name(&mut buf, 1, 4, 2);
                assert_eq!(buf, [1, 5, 6, 4, 2, 3]);
            }

            #[test]
            fn $name2() {
                let mut buf = [1, 2, 3, 4, 5, 6];
                super::$name(&mut buf, 0, 3, 0);
                assert_eq!(buf, [1, 2, 3, 4, 5, 6]);
            }

            #[test]
            #[should_panic]
            fn $name3() {
                let mut buf = [1, 2, 3, 4, 5, 6];
                super::$name(&mut buf, 1, 5, 3);
            }
        }
    }

    swap_test!(
        swap_sequence, swap_sequence_adjacent, swap_sequence_disjoint, swap_sequence_zero, swap_sequence_panic
    );
    swap_test!(
        swap_unchecked, swap_unchecked_adjacent, swap_unchecked_disjoint, swap_unchecked_zero, swap_unchecked_panic
    );

    #[test]
    fn swap_inline_adjacent() {
        let mut buf = [1, 2, 3, 4, 5, 6];
        super::swap_inline(&mut buf, 3);
        assert_eq!(buf, [4, 5, 6, 1, 2, 3]);
    }

    #[test]
    fn swap_inline_disjoint() {
        let mut buf = [1, 2, 3, 4, 5, 6];
        super::swap_inline(&mut buf[1 .. 6], 2);
        assert_eq!(buf, [1, 5, 6, 4, 2, 3]);
    }

    #[test]
    fn swap_inline_zero() {
        let mut buf = [1, 2, 3, 4, 5, 6];
        super::swap_inline(&mut buf, 0);
        assert_eq!(buf, [1, 2, 3, 4, 5, 6]);
    }

    #[test]
    #[should_panic]
    fn swap_inline_panic() {
        let mut buf = [1, 2, 3, 4, 5, 6];
        super::swap_inline(&mut buf, 5);
    }

    macro_rules! swap_bench {
        ($name:ident, $func:ident, $len:expr) => {
            #[bench]
            fn $name(b: &mut Bencher) {
                let mut a = vec![0i64; $len];
                b.iter(|| super::$func(&mut a, 0, $len / 2, $len / 2));
            }
        }
    }

    macro_rules! swap_bench_new_sig {
        ($name:ident, $func:ident, $len:expr) => {
            #[bench]
            fn $name(b: &mut Bencher) {
                let mut a = vec![0i64; $len];
                b.iter(|| super::$func(&mut a, $len / 2));
            }
        }
    }

    swap_bench!(swap_2_sequence, swap_sequence, 100);
    swap_bench!(swap_2_unchecked, swap_unchecked, 100);
    swap_bench_new_sig!(swap_2_inline, swap_inline, 100);

    swap_bench!(swap_4_sequence, swap_sequence, 10_000);
    swap_bench!(swap_4_unchecked, swap_unchecked, 10_000);
    swap_bench_new_sig!(swap_4_inline, swap_inline, 10_000);

    swap_bench!(swap_8_sequence, swap_sequence, 100_000_000);
    swap_bench!(swap_8_unchecked, swap_unchecked, 100_000_000);
    swap_bench_new_sig!(swap_8_inline, swap_inline, 100_000_000);

    macro_rules! rotate_test {
        ($name:ident, $name0:ident, $name1:ident, $nameg1:ident, $nameg3:ident) => {
            #[test]
            fn $name0() {
                let mut buf: [i32; 0] = [];
                super::$name(&mut buf, 0);
                assert_eq!(buf, []);
            }

            #[test]
            fn $name1() {
                let mut buf = [5, 4];
                super::$name(&mut buf, 1);
                assert_eq!(buf, [4, 5]);
            }

            #[test]
            fn $nameg1() {
                let mut buf = [5, 4, 3, 2, 1];
                super::$name(&mut buf, 2);
                assert_eq!(buf, [2, 1, 5, 4, 3]);
            }

            #[test]
            fn $nameg3() {
                let mut buf = [1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21];
                super::$name(&mut buf, 6);
                assert_eq!(buf, [16, 17, 18, 19, 20, 21, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15]);
            }
        }
    }
    rotate_test!(rotate_stride, rotate_stride_0, rotate_stride_1, rotate_stride_gcd1, rotate_stride_gcd3);
    rotate_test!(rotate_stride_addmod, rotate_stride_addmod_0, rotate_stride_addmod_1, rotate_stride_addmod_gcd1, rotate_stride_addmod_gcd3);
    rotate_test!(rotate_stride_unchecked, rotate_stride_unchecked_0, rotate_stride_unchecked_1, rotate_stride_unchecked_gcd1, rotate_stride_unchecked_gcd3);
    rotate_test!(rotate_block, rotate_block_0, rotate_block_1, rotate_block_gcd1, rotate_block_gcd3);
    rotate_test!(rotate_block_addmod, rotate_block_addmod_0, rotate_block_addmod_1, rotate_block_addmod_gcd1, rotate_block_addmod_gcd3);
    rotate_test!(rotate_block_unchecked, rotate_block_unchecked_0, rotate_block_unchecked_1, rotate_block_unchecked_gcd1, rotate_block_unchecked_gcd3);
    rotate_test!(rotate_block_unchecked_addmod, rotate_block_unchecked_addmod_0, rotate_block_unchecked_addmod_1, rotate_block_unchecked_addmod_gcd1, rotate_block_unchecked_addmod_gcd3);
    rotate_test!(rotate_block_swap, rotate_block_swap_0, rotate_block_swap_1, rotate_block_swap_gcd1, rotate_block_swap_gcd3);
    rotate_test!(rotate_block_adapt, rotate_block_adapt_0, rotate_block_adapt_1, rotate_adapt_gcd1, rotate_adapt_gcd3);
    rotate_test!(rotate_adapt_gcd, rotate_adapt_gcd_0, rotate_adapt_gcd_1, rotate_adapt_gcd_gcd1, rotate_adapt_gcd_gcd3);
    rotate_test!(rotate_adapt_gcd_unsafe, rotate_adapt_gcd_unsafe_0, rotate_adapt_gcd_unsafe_1, rotate_adapt_gcd_unsafe_gcd1, rotate_adapt_gcd_unsafe_gcd3);
    rotate_test!(rotate_adapt_gcd_no_overflow, rotate_adapt_gcd_no_overflow_0, rotate_adapt_gcd_no_overflow_1, rotate_adapt_gcd_no_overflow_gcd1, rotate_adapt_gcd_no_overflow_gcd3);

    macro_rules! rotate_bench {
        ($name:ident, $func:ident, $len:expr, $k:expr) => {
            #[bench]
            fn $name(b: &mut Bencher) {
                let mut a = vec![0i64; $len];
                b.iter(|| super::$func(&mut a, $k));
            }
        }
    }

    rotate_bench!(rotate_2_40_stride, rotate_stride, 100, 40);
    rotate_bench!(rotate_2_40_stride_addmod, rotate_stride_addmod, 100, 40);
    rotate_bench!(rotate_2_40_stride_unchecked, rotate_stride_unchecked, 100, 40);
    rotate_bench!(rotate_2_40_block, rotate_block, 100, 40);
    rotate_bench!(rotate_2_40_block_addmod, rotate_block_addmod, 100, 40);
    rotate_bench!(rotate_2_40_block_unchecked, rotate_block_unchecked, 100, 40);
    rotate_bench!(rotate_2_40_block_unchecked_addmod, rotate_block_unchecked_addmod, 100, 40);
    rotate_bench!(rotate_2_40_block_swap, rotate_block_swap, 100, 40);
    rotate_bench!(rotate_2_40_block_adapt, rotate_block_adapt, 100, 40);
    rotate_bench!(rotate_2_40_adapt_gcd, rotate_adapt_gcd, 100, 40);
    rotate_bench!(rotate_2_40_adapt_gcd_unsafe, rotate_adapt_gcd_unsafe, 100, 40);
    rotate_bench!(rotate_2_40_adapt_gcd_noof, rotate_adapt_gcd_no_overflow, 100, 40);

    rotate_bench!(rotate_4_4000_stride, rotate_stride, 10000, 4000);
    rotate_bench!(rotate_4_4000_stride_addmod, rotate_stride_addmod, 10000, 4000);
    rotate_bench!(rotate_4_4000_stride_unchecked, rotate_stride_unchecked, 10000, 4000);
    rotate_bench!(rotate_4_4000_block, rotate_block, 10000, 4000);
    rotate_bench!(rotate_4_4000_block_addmod, rotate_block_addmod, 10000, 4000);
    rotate_bench!(rotate_4_4000_block_unchecked, rotate_block_unchecked, 10000, 4000);
    rotate_bench!(rotate_4_4000_block_unchecked_addmod, rotate_block_unchecked_addmod, 10000, 4000);
    rotate_bench!(rotate_4_4000_block_swap, rotate_block_swap, 10000, 4000);
    rotate_bench!(rotate_4_4000_block_adapt, rotate_block_adapt, 10000, 4000);
    rotate_bench!(rotate_4_4000_adapt_gcd, rotate_adapt_gcd, 10000, 4000);
    rotate_bench!(rotate_4_4000_adapt_gcd_unsafe, rotate_adapt_gcd_unsafe, 10000, 4000);
    rotate_bench!(rotate_4_4000_adapt_gcd_noof, rotate_adapt_gcd_no_overflow, 10000, 4000);

    rotate_bench!(rotate_4_7003_stride, rotate_stride, 10000, 7003);
    rotate_bench!(rotate_4_7003_stride_addmod, rotate_stride_addmod, 10000, 7003);
    rotate_bench!(rotate_4_7003_stride_unchecked, rotate_stride_unchecked, 10000, 7003);
    rotate_bench!(rotate_4_7003_block, rotate_block, 10000, 7003);
    rotate_bench!(rotate_4_7003_block_addmod, rotate_block_addmod, 10000, 7003);
    rotate_bench!(rotate_4_7003_block_unchecked, rotate_block_unchecked, 10000, 7003);
    rotate_bench!(rotate_4_7003_block_unchecked_addmod, rotate_block_unchecked_addmod, 10000, 7003);
    rotate_bench!(rotate_4_7003_block_swap, rotate_block_swap, 10000, 7003);
    rotate_bench!(rotate_4_7003_block_adapt, rotate_block_adapt, 10000, 7003);
    rotate_bench!(rotate_4_7003_adapt_gcd, rotate_adapt_gcd, 10000, 7003);
    rotate_bench!(rotate_4_7003_adapt_gcd_unsafe, rotate_adapt_gcd_unsafe, 10000, 7003);
    rotate_bench!(rotate_4_7003_adapt_gcd_noof, rotate_adapt_gcd_no_overflow, 10000, 7003);

    rotate_bench!(rotate_4_42_stride, rotate_stride, 10000, 42);
    rotate_bench!(rotate_4_42_stride_addmod, rotate_stride_addmod, 10000, 42);
    rotate_bench!(rotate_4_42_stride_unchecked, rotate_stride_unchecked, 10000, 42);
    rotate_bench!(rotate_4_42_block, rotate_block, 10000, 42);
    rotate_bench!(rotate_4_42_block_addmod, rotate_block_addmod, 10000, 42);
    rotate_bench!(rotate_4_42_block_unchecked, rotate_block_unchecked, 10000, 42);
    rotate_bench!(rotate_4_42_block_unchecked_addmod, rotate_block_unchecked_addmod, 10000, 42);
    rotate_bench!(rotate_4_42_block_swap, rotate_block_swap, 10000, 42);
    rotate_bench!(rotate_4_42_block_adapt, rotate_block_adapt, 10000, 42);
    rotate_bench!(rotate_4_42_adapt_gcd, rotate_adapt_gcd, 10000, 42);
    rotate_bench!(rotate_4_42_adapt_gcd_unsafe, rotate_adapt_gcd_unsafe, 10000, 42);
    rotate_bench!(rotate_4_42_adapt_gcd_noof, rotate_adapt_gcd_no_overflow, 10000, 42);

    rotate_bench!(rotate_8_4000_block, rotate_block, 100_000_000, 4000);
    rotate_bench!(rotate_8_4000_block_addmod, rotate_block_addmod, 100_000_000, 4000);
    rotate_bench!(rotate_8_4000_block_unchecked, rotate_block_unchecked, 100_000_000, 4000);
    rotate_bench!(rotate_8_4000_block_unchecked_addmod, rotate_block_unchecked_addmod, 100_000_000, 4000);
    rotate_bench!(rotate_8_4000_block_swap, rotate_block_swap, 100_000_000, 4000);
    rotate_bench!(rotate_8_4000_block_adapt, rotate_block_adapt, 100_000_000, 4000);
    rotate_bench!(rotate_8_4000_adapt_gcd, rotate_adapt_gcd, 100_000_000, 4000);
    rotate_bench!(rotate_8_4000_adapt_gcd_unsafe, rotate_adapt_gcd_unsafe, 100_000_000, 4000);
    rotate_bench!(rotate_8_4000_adapt_gcd_noof, rotate_adapt_gcd_no_overflow, 100_000_000, 4000);

    // GCD 2
    rotate_bench!(rotate_8_42_block_unchecked, rotate_block_unchecked, 100_000_000, 42);
    rotate_bench!(rotate_8_42_block_unchecked_addmod, rotate_block_unchecked_addmod, 100_000_000, 42);
    rotate_bench!(rotate_8_42_block_swap, rotate_block_swap, 100_000_000, 42);
    rotate_bench!(rotate_8_42_block_adapt, rotate_block_adapt, 100_000_000, 42);
    rotate_bench!(rotate_8_42_adapt_gcd, rotate_adapt_gcd, 100_000_000, 42);
    rotate_bench!(rotate_8_42_adapt_gcd_unsafe, rotate_adapt_gcd_unsafe, 100_000_000, 42);
    rotate_bench!(rotate_8_42_adapt_gcd_noof, rotate_adapt_gcd_no_overflow, 100_000_000, 42);

    // Prime
    rotate_bench!(rotate_8_500009_adapt_gcd, rotate_adapt_gcd, 100_000_000, 500_009);
    rotate_bench!(rotate_8_500009_adapt_gcd_unsafe, rotate_adapt_gcd_unsafe, 100_000_000, 500_009);
    rotate_bench!(rotate_8_500009_adapt_gcd_noof, rotate_adapt_gcd_no_overflow, 100_000_000, 500_009);
}

