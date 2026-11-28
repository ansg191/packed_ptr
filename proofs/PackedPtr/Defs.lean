import Aeneas
open Aeneas Aeneas.Std

namespace PackedPtr

-- The upper m bits and lower n bits don't overlap
def valid_config (m n : Nat) : Prop :=
  m + n ≤ Usize.numBits

-- The address is 0 in the upper m bits
def addr_fits (addr m : Nat) : Prop :=
  addr < 2 ^ (Usize.numBits - m)

-- The address is aligned to n bits (0 in the lower n bits)
def addr_aligned (addr n : Nat) : Prop :=
  addr % 2 ^ n = 0

-- Safety condition for clean addresses (aligned to n bits & 0 in the upper m bits)
def clean_addr (addr m n : Nat) : Prop :=
  addr_aligned addr n ∧ addr_fits addr m

-- The data fits in the m + n bits available
def data_fits (data m n : Nat) : Prop :=
  data < 2 ^ (m + n)

def pack (addr data m n : Nat) : Nat :=
  addr
    + data % 2 ^ n
    + data / 2 ^ n % 2 ^ m * 2 ^ (Usize.numBits - m)

-- Clear the upper m bits and the lower n bits of a packed value
def unpack_addr (packed m n : Nat) : Nat :=
  packed % 2 ^ (Usize.numBits - m) / 2 ^ n * 2 ^ n

-- Rebuild the data from the lower n bits and the upper m bits of a packed value
def unpack_data (packed m n : Nat) : Nat :=
  packed % 2 ^ n
    + packed / 2 ^ (Usize.numBits - m) * 2 ^ n

end PackedPtr
