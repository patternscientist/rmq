import RMQ.Core.SuccinctFinal

open RMQ
open RMQ.Cartesian
open RMQ.SuccinctFinal

namespace DpR9B

abbrev Sh := Cartesian.CartesianShape

def sup (s : Sh) : Nat := builtRelativeSplitBPCloseRankSuperOverhead s
def blk (s : Sh) : Nat := builtRelativeSplitBPCloseRankBlockOverhead s

def wOf (n : Nat) : Nat := SuccinctRank.machineWordBits (2 * n)
def bwOf (n : Nat) : Nat := SuccinctRank.machineWordBits (wOf n * wOf n)
def supOfN (n : Nat) : Nat :=
  (2 * n / wOf n / wOf n + 1) * wOf n + (2 * n / wOf n / wOf n + 1) * wOf n
def blkOfN (n : Nat) : Nat :=
  (2 * n / wOf n + 1) * bwOf n + (2 * n / wOf n + 1) * bwOf n

def leftSpine : Nat -> Sh
  | 0 => .empty
  | n + 1 => .node (leftSpine n) .empty

def rightSpine : Nat -> Sh
  | 0 => .empty
  | n + 1 => .node .empty (rightSpine n)

def balanced : Nat -> Sh
  | 0 => .empty
  | n + 1 => .node (balanced (n / 2)) (balanced (n - n / 2))

def combAux : Nat -> Sh
  | 0 => .empty
  | 1 => .node .empty .empty
  | n + 2 => .node (.node .empty .empty) (combAux n)

/-- deterministic pseudo-random shape, fuel-driven so it is structurally
    recursive and cheap to evaluate. -/
def pseudoF : Nat -> Nat -> Nat -> Sh
  | 0, _, _ => .empty
  | _, _, 0 => .empty
  | fuel + 1, seed, n + 1 =>
      let s := (seed * 1103515245 + 12345) % 2147483648
      let k := s % (n + 1)
      .node (pseudoF fuel (s + 1) k) (pseudoF fuel (s + 2) (n - k))

def pseudo (seed n : Nat) : Sh := pseudoF (n + 1) seed n

def family (n : Nat) : List Sh :=
  [leftSpine n, rightSpine n, balanced n, combAux n,
   pseudo 1 n, pseudo 7 n, pseudo 991 n, pseudo 424242 n]

#eval show IO Unit from do
  IO.println "== REGIME SWEEP: n | superSampleCount | blockSampleCount | allSizesOk | distinct (sup,blk) | #distinctBpCodes | closedFormOk =="
  for n in [0,1,2,3,4,8,16,31,32,33,63,64,65,100,127,128,129,200,255,256,257,400,512,600,1000] do
    let fam := family n
    let sizesOk := fam.all (fun s => s.size == n)
    let pairs := (fam.map (fun s => (sup s, blk s))).eraseDups
    let codes := (fam.map (fun s => s.bpCode)).eraseDups
    let scnt := 2 * n / wOf n / wOf n + 1
    let bcnt := 2 * n / wOf n + 1
    let okClosed := pairs == [(supOfN n, blkOfN n)]
    IO.println s!"{n} | sCnt={scnt} | bCnt={bcnt} | sizesOk={sizesOk} | pairs={pairs} | codes={codes.length} | closedOk={okClosed}"

end DpR9B
