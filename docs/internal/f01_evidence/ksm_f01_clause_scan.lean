import RMQ.Core.SuccinctFinalStoreParam

/-! Which conjunct of `Active` fails, as a function of n?  Exploratory `#eval`. -/

namespace KsmClause

def base (n : Nat) : Nat := Nat.log2 n + 1
def blockSizeRaw (n : Nat) : Nat := 2 * base n
def bpsRaw (n : Nat) : Nat := base n
def blockCountRaw (n : Nat) : Nat := n / base n
def superCountRaw (n : Nat) : Nat := blockCountRaw n / bpsRaw n + 1
def superWidth (n : Nat) : Nat := Nat.log2 (2 * n) + 1
def relWidthRaw (n : Nat) : Nat := 2 * (Nat.log2 (base n) + 1) + 3

def c1 (n : Nat) : Bool := decide (blockCountRaw n * blockSizeRaw n <= 2 * n)
def c2 (n : Nat) : Bool := decide (2 * (bpsRaw n * blockSizeRaw n) < 2 ^ relWidthRaw n)
def c3 (n : Nat) : Bool := decide (blockSizeRaw n < 2 ^ relWidthRaw n)
def c4 (n : Nat) : Bool := decide (superCountRaw n * superWidth n <= 16 * (n / (Nat.log2 n + 1)))
def c5 (n : Nat) : Bool := decide (3 * (blockCountRaw n * relWidthRaw n) <=
    64 * ((n / (Nat.log2 n + 1)) * (Nat.log2 (Nat.log2 n + 1) + 1)))
def c6 (n : Nat) : Bool := decide (relWidthRaw n <= Nat.log2 (2 * n) + 1)

def cs : List (String × (Nat -> Bool)) :=
  [("c1", c1), ("c2", c2), ("c3", c3), ("c4", c4), ("c5", c5), ("c6", c6)]

def flips (f : Nat -> Bool) (lo hi : Nat) : List (Nat × Bool) :=
  (List.range' lo (hi - lo)).filterMap (fun n =>
    if n = lo then some (n, f n)
    else if f n = f (n - 1) then none else some (n, f n))

#eval cs.map (fun p => (p.1, flips p.2 0 70000))

-- exact witness data at the flip points
#eval [0,1,2,511,512,999,1000,1023,1024,1330,1331].map (fun n =>
  (n, Nat.log2 n, Nat.log2 (2*n), Nat.log2 (base n), base n, blockCountRaw n,
   superCountRaw n, relWidthRaw n, superWidth n,
   c1 n, c2 n, c3 n, c4 n, c5 n, c6 n,
   decide (base n * base n <= n / base n)))

end KsmClause
