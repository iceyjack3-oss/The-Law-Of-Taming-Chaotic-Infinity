import Mathlib.Data.Nat.Bits
import Mathlib.Data.Nat.Log
import Mathlib.Data.Nat.Size
import Mathlib.Tactic.Order
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Mathlib.Tactic.IntervalCases

def bitLength (n : Nat) : Nat :=
  if n = 0 then 0 else Nat.log2 n + 1

theorem bitLength_lower_pow {n : Nat} (hn : 0 < n) :
    2 ^ (bitLength n - 1) ≤ n := by
  have hlen : bitLength n = Nat.log 2 n + 1 := by
    simp [bitLength, Nat.ne_of_gt hn, Nat.log2_eq_log_two]
  rw [hlen, Nat.add_sub_cancel_right]
  exact Nat.pow_log_le_self 2 (Nat.ne_of_gt hn)

theorem lt_pow_bitLength {n : Nat} (hn : 0 < n) :
    n < 2 ^ bitLength n := by
  have hlen : bitLength n = Nat.log 2 n + 1 := by
    simp [bitLength, Nat.ne_of_gt hn, Nat.log2_eq_log_two]
  rw [hlen, Nat.pow_succ]
  exact Nat.lt_pow_succ_log_self Nat.one_lt_two n

theorem size_eq_bitLength {n : Nat} (hn : 0 < n) : Nat.size n = bitLength n := by
  have hupper : Nat.size n ≤ bitLength n :=
    (Nat.size_le).2 (lt_pow_bitLength hn)
  have hlower : bitLength n - 1 < Nat.size n :=
    (Nat.lt_size).2 (bitLength_lower_pow hn)
  omega

def maskBitsFromMSB : List Bool → Nat → List Bool
  | [], _ => []
  | bit :: rest, index =>
      (if index < 2 ∨ index % 4 = 0 then false else bit) ::
        maskBitsFromMSB rest (index + 1)

def bitsToNat : List Bool → Nat
  | [] => 0
  | bit :: rest => (if bit then 2 ^ rest.length else 0) + bitsToNat rest

theorem bitsToNat_append_singleton (bits : List Bool) (bit : Bool) :
    bitsToNat (bits ++ [bit]) = 2 * bitsToNat bits + bit.toNat := by
  induction bits with
  | nil => cases bit <;> simp [bitsToNat]
  | cons head rest ih =>
      cases head with
      | false => simp [bitsToNat, ih]
      | true => simp [bitsToNat, ih, Nat.pow_succ]; ring

theorem bitsToNat_append (pre suffix : List Bool) :
    bitsToNat (pre ++ suffix) =
      bitsToNat pre * 2 ^ suffix.length + bitsToNat suffix := by
  induction pre with
  | nil => simp [bitsToNat]
  | cons bit rest ih =>
      cases bit with
      | false => simp [bitsToNat, ih]
      | true => simp [bitsToNat, ih]; ring

theorem bitsToNat_take_drop_two (bits : List Bool) :
    bitsToNat bits =
      bitsToNat (bits.take 2) * 2 ^ (bits.drop 2).length + bitsToNat (bits.drop 2) := by
  calc
    bitsToNat bits = bitsToNat (bits.take 2 ++ bits.drop 2) := by
      rw [List.take_append_drop]
    _ = _ := bitsToNat_append _ _

theorem bitsToNat_natBits (n : Nat) : bitsToNat (Nat.bits n).reverse = n := by
  induction n using Nat.binaryRec' with
  | zero => simp [bitsToNat]
  | bit bit n h ih =>
      rw [Nat.bits_append_bit n bit h, List.reverse_cons]
      rw [bitsToNat_append_singleton, ih, Nat.bit_val]

theorem bitsToNat_lt_two_pow_length (bits : List Bool) :
    bitsToNat bits < 2 ^ bits.length := by
  induction bits with
  | nil => simp [bitsToNat]
  | cons bit rest ih =>
      cases bit <;> simp [bitsToNat, Nat.pow_succ] at * <;> omega

theorem maskBitsFromMSB_length (bits : List Bool) (index : Nat) :
    (maskBitsFromMSB bits index).length = bits.length := by
  induction bits generalizing index with
  | nil => rfl
  | cons bit rest ih => simp [maskBitsFromMSB, ih]

theorem bitsToNat_maskBits_le (bits : List Bool) (index : Nat) :
    bitsToNat (maskBitsFromMSB bits index) ≤ bitsToNat bits := by
  induction bits generalizing index with
  | nil => simp [maskBitsFromMSB, bitsToNat]
  | cons bit rest ih =>
      have hlen := maskBitsFromMSB_length rest (index + 1)
      by_cases hmask : index < 2 ∨ index % 4 = 0
      · cases bit with
        | false =>
            simp [maskBitsFromMSB, bitsToNat, hmask]
            exact ih (index + 1)
        | true =>
            simp only [maskBitsFromMSB]
            have htail := ih (index + 1)
            simp [hmask, bitsToNat]
            exact htail.trans (Nat.le_add_left _ _)
      · cases bit <;> simp [maskBitsFromMSB, bitsToNat, hmask, hlen, ih]

theorem bitsToNat_maskBits_top_two_le_tail (first second : Bool) (tail : List Bool) :
    bitsToNat (maskBitsFromMSB (first :: second :: tail) 0) ≤ bitsToNat tail := by
  simpa [maskBitsFromMSB, bitsToNat] using bitsToNat_maskBits_le tail 2

theorem bitsToNat_maskBits_le_drop_two (bits : List Bool) :
    bitsToNat (maskBitsFromMSB bits 0) ≤ bitsToNat (bits.drop 2) := by
  cases bits with
  | nil => simp [maskBitsFromMSB, bitsToNat]
  | cons first rest =>
      cases rest with
      | nil => simp [maskBitsFromMSB, bitsToNat]
      | cons second tail =>
          simpa [maskBitsFromMSB, bitsToNat] using
            bitsToNat_maskBits_le tail 2

def maskedValue (n : Nat) : Nat :=
  bitsToNat (maskBitsFromMSB (Nat.bits (3 * n + 1)).reverse 0)

theorem maskedValue_le_trajectory (n : Nat) : maskedValue n ≤ 3 * n + 1 := by
  unfold maskedValue
  calc
    bitsToNat (maskBitsFromMSB (Nat.bits (3 * n + 1)).reverse 0) ≤
        bitsToNat ((Nat.bits (3 * n + 1)).reverse) := bitsToNat_maskBits_le _ _
    _ = 3 * n + 1 := bitsToNat_natBits _

theorem maskedValue_le_suffix (n : Nat) :
    maskedValue n ≤ bitsToNat ((Nat.bits (3 * n + 1)).reverse.drop 2) := by
  exact bitsToNat_maskBits_le_drop_two _

def drainTrailingZeros (n : Nat) : Nat :=
  if n = 0 then 0 else if n % 2 = 0 then drainTrailingZeros (n / 2) else n
termination_by n
decreasing_by omega

theorem drainTrailingZeros_le (n : Nat) : drainTrailingZeros n ≤ n := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
      by_cases hzero : n = 0
      · simp [drainTrailingZeros, hzero]
      · by_cases heven : n % 2 = 0
        · have hlt : n / 2 < n := Nat.div_lt_self (by omega) (by decide)
          have hrec := ih (n / 2) hlt
          rw [drainTrailingZeros]
          simp only [hzero, heven]
          exact hrec.trans (Nat.div_le_self n 2)
        · simp [drainTrailingZeros, hzero, heven]

def nextState (n : Nat) : Nat :=
  if bitLength n ≤ 8 then
    n / 2
  else
    drainTrailingZeros (maskedValue n)

theorem nextState_large_strictly_decreases {n : Nat}
    (hlarge : bitLength n > 8) : nextState n < n := by
  have hn : 0 < n := by
    by_contra h
    have : n = 0 := by omega
    simp [bitLength, this] at hlarge
  let L := bitLength n
  let V := 3 * n + 1
  have hL : 0 < L := by dsimp [L]; omega
  have hnlo : 2 ^ (L - 1) ≤ n := by
    dsimp [L]
    exact bitLength_lower_pow hn
  have hnhi : n < 2 ^ L := by
    dsimp [L]
    exact lt_pow_bitLength hn
  have hlog : L = Nat.log 2 n + 1 := by
    dsimp [L, bitLength]
    simp [Nat.ne_of_gt hn, Nat.log2_eq_log_two]
  have hnloglo : 2 ^ Nat.log 2 n ≤ n :=
    Nat.pow_log_le_self 2 (Nat.ne_of_gt hn)
  have hpowLog : 2 ^ L = 2 * 2 ^ Nat.log 2 n := by
    rw [hlog, Nat.pow_succ]
    ring
  have hVlo : 2 ^ L ≤ V := by
    rw [hpowLog]
    dsimp [V]
    omega
  have hVhi : V < 2 ^ (L + 2) := by
    dsimp [V]
    calc
      3 * n + 1 ≤ 4 * n := by omega
      _ < 4 * 2 ^ L := by omega
      _ = 2 ^ (L + 2) := by
        rw [show L + 2 = (L + 1) + 1 by omega, Nat.pow_succ,
          Nat.pow_succ]
        ring
  have hsizeLo : L < Nat.size V := (Nat.lt_size).2 hVlo
  have hsizeHi : Nat.size V ≤ L + 2 := (Nat.size_le).2 hVhi
  have hsizeCases : Nat.size V = L + 1 ∨ Nat.size V = L + 2 := by omega
  let bs := (Nat.bits V).reverse
  let suffix := bs.drop 2
  let prefixVal := bitsToNat (bs.take 2)
  have hbslen : bs.length = Nat.size V := by
    dsimp [bs]
    simp [Nat.size_eq_bits_len]
  have hsuflen : suffix.length = Nat.size V - 2 := by
    dsimp [suffix]
    rw [List.length_drop, hbslen]
  have hsufpow : bitsToNat suffix < 2 ^ suffix.length :=
    bitsToNat_lt_two_pow_length suffix
  have hmask : maskedValue n ≤ bitsToNat suffix := by
    dsimp [suffix, bs, V]
    exact maskedValue_le_suffix n
  have hVbits : bitsToNat bs = V := by
    dsimp [bs]
    exact bitsToNat_natBits V
  have hdecomp : V = prefixVal * 2 ^ suffix.length + bitsToNat suffix := by
    dsimp [prefixVal, suffix]
    rw [← hVbits]
    exact bitsToNat_take_drop_two bs
  have hprefix : prefixVal < 4 := by
    have hp := bitsToNat_lt_two_pow_length (bs.take 2)
    have hlen : (bs.take 2).length ≤ 2 := by simp
    have hpow : 2 ^ (bs.take 2).length ≤ 4 := by
      calc
        2 ^ (bs.take 2).length ≤ 2 ^ 2 := Nat.pow_le_pow_right (by decide) hlen
        _ = 4 := by norm_num
    omega
  have hbaseDecrease : bitsToNat suffix < n := by
    rcases hsizeCases with hs | hs
    · have hlen : suffix.length = L - 1 := by rw [hsuflen, hs]; omega
      rw [hlen] at hsufpow
      exact hsufpow.trans_le hnlo
    · have hlen : suffix.length = L := by rw [hsuflen, hs]; omega
      have hq : 2 ^ (L + 1) = 2 * 2 ^ L := by
        rw [Nat.pow_succ]
        ring
      have hVlow' : 2 ^ (L + 1) ≤ V := by
        exact (Nat.lt_size).1 (by omega)
      have hVhi' : V < 3 * 2 ^ L := by
        have hgap : n + 1 ≤ 2 ^ L := Nat.succ_le_of_lt hnhi
        have hgap3 : 3 * (n + 1) ≤ 3 * 2 ^ L := Nat.mul_le_mul_left 3 hgap
        dsimp [V]
        omega
      rw [hq] at hVlow'
      have hprefixEq : prefixVal = 2 := by
        rw [hlen] at hdecomp
        have hsuflt : bitsToNat suffix < 2 ^ L := by simpa [hlen] using hsufpow
        interval_cases prefixVal <;> omega
      rw [hlen, hprefixEq] at hdecomp
      dsimp [V] at hdecomp
      omega
  have hnext : nextState n = drainTrailingZeros (maskedValue n) := by
    simp [nextState, Nat.not_le_of_gt hlarge]
  rw [hnext]
  exact lt_of_le_of_lt (drainTrailingZeros_le (maskedValue n))
    (lt_of_le_of_lt hmask hbaseDecrease)

def tamingSystem (fuel n : Nat) : Nat :=
  match fuel with
  | 0 => n
  | Nat.succ remaining =>
      if n ≤ 1 then n else tamingSystem remaining (nextState n)

theorem nextState_small_strictly_decreases {n : Nat}
    (hbase : 1 < n) (hsmall : bitLength n ≤ 8) : nextState n < n := by
  simp [nextState, hsmall]
  omega

theorem tamingSystem_returns_baseline (fuel n : Nat) (hbase : n ≤ 1) :
    tamingSystem fuel n = n := by
  induction fuel with
  | zero => rfl
  | succ fuel ih => simp [tamingSystem, hbase]

theorem tamingSystem_eventually_baseline (n : Nat) :
    ∃ fuel, tamingSystem fuel n ≤ 1 := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
      by_cases hbase : n ≤ 1
      · exact ⟨0, hbase⟩
      · have hactive : 1 < n := by omega
        by_cases hsmall : bitLength n ≤ 8
        · have hstep := nextState_small_strictly_decreases hactive hsmall
          obtain ⟨fuel, hdone⟩ := ih (nextState n) hstep
          refine ⟨fuel + 1, ?_⟩
          simpa [tamingSystem, hbase] using hdone
        · have hlarge : bitLength n > 8 := by omega
          have hstep := nextState_large_strictly_decreases hlarge
          obtain ⟨fuel, hdone⟩ := ih (nextState n) hstep
          refine ⟨fuel + 1, ?_⟩
          simpa [tamingSystem, hbase] using hdone
