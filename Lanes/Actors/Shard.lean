/-
Copyright (c) 2026 The Lanes Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Lanes.Actors.System
public import Lanes.Data.Codec
public import Lanes.Data.Frame

/-!
# A system as one shard sees it

`System.shard sys hosts` is `sys` on a shard that hosts only some of its actors. The actors it
hosts are themselves, except that a message to an actor hosted elsewhere leaves the shard as an
output, a `Parcel`, and a parcel arriving from elsewhere is an input. An actor the shard does
not host only forwards what reaches it, so a misrouted message is passed on, never handled in
the wrong place.

It is an ordinary `System`, so a shard runs on the ordinary kernel and runtime, and keeps the
ordinary journal. Shards in different processes, joined by TCP, are `Lanes.Peers`.
-/

@[expose] public section

namespace Lanes

variable {σ : Signature}

/-- A message with its receiver, as it travels between shards. -/
abbrev Parcel (σ : Signature) : Type := (i : σ.Id) × σ.Msg i

abbrev shardSig (σ : Signature) : Signature where
  Id := σ.Id
  Msg := σ.Msg
  In := σ.In ⊕ Parcel σ
  Out := σ.Out ⊕ Parcel σ

def shardEffect (hosts : σ.Id → Bool) {i : σ.Id} : Effect σ i → Effect (shardSig σ) i
  | .send to msg => if hosts to then .send to msg else .emit (.inr ⟨to, msg⟩)
  | .emit out => .emit (.inl out)
  | .after delay_ms msg => .after delay_ms msg
  | .cancel msg => .cancel msg
  | .stop => .stop

abbrev System.shard (sys : System σ) (hosts : σ.Id → Bool) : System (shardSig σ) where
  State := sys.State
  actor i :=
    if hosts i then (sys.actor i).mapEff fun eff => [shardEffect hosts eff]
    else
      { init := (sys.actor i).init
        step := fun s msg => (s, [.emit (.inr ⟨i, msg⟩)])
        recover := fun s => (s, []) }
  accept
    | .inl x => sys.accept x
    | .inr parcel => parcel
  boot := sys.boot.filter hosts

/-! A parcel as bytes, for shards in different processes: one frame per parcel, so that a
stream of them can be read as it arrives. -/

namespace Parcel

variable (id : Codec σ.Id) (msg : ∀ i, Codec (σ.Msg i))

def payload (parcel : Parcel σ) : ByteArray :=
  Frame.encode ((Codec.sigma id msg).write parcel)

def ofPayload (bytes : ByteArray) : Option (Parcel σ) :=
  match (Codec.sigma id msg).read (Frame.decode bytes) with
  | some (parcel, []) => some parcel
  | _ => none

def fits (parcel : Parcel σ) : Bool :=
  ((Codec.sigma id msg).write parcel).all Frame.fits && Frame.fits (payload id msg parcel)

def send (parcels : List (Parcel σ)) : ByteArray :=
  Frame.encode (parcels.map (payload id msg))

/-- The parcels wholly received so far and the bytes they took; what follows those bytes is a
parcel still arriving. `none` if the bytes are not the start of a stream of parcels: a frame
that is all there and does not check, or one that is not a parcel. -/
def receive (received : ByteArray) : Option (List (Parcel σ) × Nat) :=
  let payloads := Frame.decode received
  if Frame.unfinished received (Frame.span payloads) then
    (payloads.mapM (ofPayload id msg)).map (·, Frame.span payloads)
  else none

theorem ofPayload_payload {parcel : Parcel σ} (h : fits id msg parcel = true) :
    ofPayload id msg (payload id msg parcel) = some parcel := by
  simp only [fits, Bool.and_eq_true] at h
  have hsound := (Codec.sigma id msg).sound parcel []
  rw [List.append_nil] at hsound
  simp [ofPayload, payload, Frame.decode_encode (Frame.all_fits_iff.mp h.1), hsound]

private theorem mapM_ofPayload {parcels : List (Parcel σ)}
    (h : ∀ parcel ∈ parcels, fits id msg parcel = true) :
    (parcels.map (payload id msg)).mapM (ofPayload id msg) = some parcels := by
  induction parcels with
  | nil => rfl
  | cons parcel parcels ih =>
    simp [ofPayload_payload id msg (h parcel List.mem_cons_self),
      ih fun p hp => h p (List.mem_cons_of_mem _ hp)]

/-- However a stream of parcels is cut, at any byte, what has arrived reads as exactly the
parcels wholly sent before the cut, in order. So a receiver that reads the stream in pieces of
any size, and takes the parcels out of what it has so far, gets the parcels that were sent. -/
theorem receive_send {parcels : List (Parcel σ)}
    (h : ∀ parcel ∈ parcels, fits id msg parcel = true) (n : Nat) :
    receive id msg ((send id msg parcels).extract 0 n)
      = some (parcels.take (Frame.whole (parcels.map (payload id msg)) n),
          Frame.span ((parcels.map (payload id msg)).take
            (Frame.whole (parcels.map (payload id msg)) n))) := by
  have hfit : ∀ p ∈ parcels.map (payload id msg), p.size < 2 ^ 32 := by
    intro p hp
    obtain ⟨parcel, hparcel, rfl⟩ := List.mem_map.mp hp
    have := h parcel hparcel
    simp only [fits, Bool.and_eq_true] at this
    exact Frame.fits_iff.mp this.2
  have htail := Frame.unfinished_take hfit n
  rw [← List.map_take] at htail
  simp only [receive, send, Frame.decode_take_eq hfit n, ← List.map_take, htail, ↓reduceIte,
    mapM_ofPayload id msg fun p hp => h p (List.mem_of_mem_take hp), Option.map_some]

end Parcel

end Lanes
