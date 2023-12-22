Simply create multiple mutable subslices of a single slice without borrow checker issues! This ain't magic and
can simply be done by oneself but this crate aims to provide a simple and safe type for doing this.

## Example

```rust
let data: & mut [u32] = & mut [1, 2, 3, 4, 5, 6, 7, 8, 9, 10];
let ndata = data.to_vec();

let mut ms = MultiSplit::new(data);

let borrow1 = ms.borrow_mut(0..5).unwrap(); // Can also borrow mutably together with other areas of this array
assert_eq!(borrow1, &ndata[0..5]);

let borrow2 = ms.borrow_mut(5..6).unwrap();
assert_eq!(borrow2, &ndata[5..6]);

// Use `borrow1` and `borrow2` together without borrow checker issues!
borrow1[0] = 3;
borrow2[0] = 7;
borrow1[1] = 1; // No borrow checker error!

// ..But a second borrow of an already borrowed range returns None!
assert_eq!(ms.borrow(0..5), None);
```

## Safety

This crate uses `unsafe`! All bounds are checked and the code has 100% test coverage!