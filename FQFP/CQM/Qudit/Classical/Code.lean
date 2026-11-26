/-
Copyright (c) 2025 Alex Meiburg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Meiburg
-/

/-
leanprover-community/physlib @ adccea9195c7c347a5f8cde1ddf6874f89ea6a9a
QuantumInfo/ClassicalInfo/Capacity.lean: list encoders and decoders, and fixed-length codes.

Modified by Shanghai Fuxi Quantum Technology Co., Ltd. in 2026
Copyright (c) 2026 Shanghai Fuxi Quantum Technology Co., Ltd.. All rights reserved.
Authors: FQFP authors
-/
module

public import FQFP.CQM.Qudit.Classical.Channel
public import Mathlib.Data.List.OfFn

/-!
# Classical codes on a memoryless channel

An encoder and decoder may change word lengths. For a fixed-length code, the output
length of each map depends only on its input length.
-/

@[expose] public noncomputable section

open Convexity

namespace Qudit

/-- A classical code with message alphabet `A` and channel alphabets `I` and `O`. -/
structure ClassicalCode (A I O : Type*) where
  /-- Encode a message for transmission. -/
  encode : List A → List I
  /-- Decode the received symbols into a message. -/
  decode : List O → List A

/-- A code whose encoded and decoded lengths depend only on the respective input lengths. -/
structure FixedLengthCode (A I O : Type*) extends ClassicalCode A I O where
  /-- Length of the encoding of an `n`-symbol message. -/
  encodedLength : ℕ → ℕ
  /-- The encoder realizes the prescribed length function on every message. -/
  length_encode (xs : List A) : (encode xs).length = encodedLength xs.length
  /-- Length of the decoding of an `n`-symbol received word. -/
  decodedLength : ℕ → ℕ
  /-- The decoder realizes the prescribed length function on every received word. -/
  length_decode (ys : List O) : (decode ys).length = decodedLength ys.length

variable {A I O : Type*} [Fintype O]

/-- Distribution of decoded messages after encoding, independent transmission, and decoding. -/
def ClassicalCode.transmit (code : ClassicalCode A I O) (C : MemorylessChannel I O)
    (xs : List A) : StdSimplex ℝ (List A) :=
  (C.onList (code.encode xs)).map (fun y => code.decode (List.ofFn y))

/-- On a deterministic channel the receiver decodes the pointwise image of the encoded word. -/
@[simp]
lemma ClassicalCode.transmit_ofFunction (code : ClassicalCode A I O) (f : I → O) (xs : List A) :
    code.transmit (.ofFunction f) xs = .single (code.decode ((code.encode xs).map f)) := by
  simp [ClassicalCode.transmit, MemorylessChannel.onList, ← List.map_ofFn, List.ofFn_get]

/-- Even on a noisy channel a fixed-length code has a deterministic decoded length. -/
lemma FixedLengthCode.map_length_transmit (code : FixedLengthCode A I O) (C : MemorylessChannel I O)
    (xs : List A) :
    (code.transmit C xs).map List.length =
      .single (code.decodedLength (code.encodedLength xs.length)) := by
  rw [ClassicalCode.transmit, ← StdSimplex.map_comp]
  simpa only [Function.comp_def, code.length_decode, List.length_ofFn, code.length_encode] using
    (StdSimplex.map_const (C.onList (code.encode xs))
      (code.decodedLength (code.encodedLength xs.length)))

end Qudit
