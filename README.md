# Packed Pointers

A configurable & generic [tagged pointer](https://en.wikipedia.org/wiki/Tagged_pointer) implementation in Rust.

A Tagged Pointer is a technique to store a value and a tag (some data) in a single pointer.
This implementation allows you to use both the LSB & MSB for the tag, configured using a generic parameter.

## Usage

### Portable Usage

```rust
use packed_ptr::PackedPtr;
use packed_ptr::config::AlignOnly;

let data = 0xdeadbeefu32;
let ptr = PackedPtr::new(&data, 1, AlignOnly).unwrap();
assert_eq!(data, unsafe { *ptr.ptr() });
assert_eq!(1, ptr.data());
```

### Platform Specific Usage

On x86_64, using level 4 paging, the 16 most significant bits are unused.
Therefore, we can pack 18 bits of data into a `*const u32`.
```rust
use packed_ptr::PackedPtr;
use packed_ptr::config::Level4Paging;

let data = 0xdeadbeefu32;
let ptr = PackedPtr::new(&data, (1 << 18) - 1, Level4Paging).unwrap();
assert_eq!(data, unsafe { *ptr.ptr() });
assert_eq!((1 << 18) - 1, ptr.data());
```

### Type Safe Data

`packed_ptr` provides a type safe interface for storing & retrieving data from a pointer.
The data must implement `Packable`, and it can be packed into a pointer using `TypedPackedPtr`.

```rust
use packed_ptr::TypedPackedPtr;
use packed_ptr::config::AlignOnly;

let data = 0xdeadbeefu32;
let packed = (true, false);
let ptr = TypedPackedPtr::new(&data, pacekd, AlignOnly).unwrap();
assert_eq!(data, unsafe { *ptr.ptr() });
assert_eq!(packed, ptr.data());
```

### References

`packed_ptr` also provides a type safe interface for storing & retrieving packed data from a reference.

```rust
use packed_ptr::PackedRef;
use packed_ptr::config::AlignOnly;

let data = 0xdeadbeefu32;
let packed = (true, false);

let ref1 = PackedRef::new(&data, packed, AlignOnly).unwrap();
assert_eq!(data, *ref1);
assert_eq!(packed, ref1.data());
```
