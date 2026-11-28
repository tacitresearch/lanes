/-
Copyright (c) 2026 The Lanes Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Lanes.Lib.Crypto.Sha256

/-!
SHA-1 (FIPS 180-4) in pure Lean, for the protocols that still name it, such as the WebSocket
handshake (RFC 6455 §4.2.2). It is broken for collisions: never use it to sign or to tell
apart what an attacker chooses. Its padding and blocks are SHA-256's. Tested against the NIST
examples; that it is SHA-1 is not proved.
-/

@[expose] public section

namespace Lanes.Sha1

abbrev State := Vector UInt32 5

def initial : State := #v[0x67452301, 0xEFCDAB89, 0x98BADCFE, 0x10325476, 0xC3D2E1F0]

def rotl (x n : UInt32) : UInt32 := (x <<< n) ||| (x >>> (32 - n))

def schedule (block : Vector UInt32 16) : Vector UInt32 80 := Id.run do
  let mut w : Vector UInt32 80 := Vector.replicate 80 0
  for h : t in [0:16] do
    have : t < 16 := h.upper
    w := w.set t block[t]
  for h : t in [16:80] do
    have : t < 80 := h.upper
    have : 16 ≤ t := h.lower
    w := w.set t (rotl (w[t - 3] ^^^ w[t - 8] ^^^ w[t - 14] ^^^ w[t - 16]) 1)
  return w

def compress (state : State) (block : Vector UInt32 16) : State := Id.run do
  let w := schedule block
  let mut a := state[0]
  let mut b := state[1]
  let mut c := state[2]
  let mut d := state[3]
  let mut e := state[4]
  for hk : t in [0:80] do
    have : t < 80 := hk.upper
    let (f, k) :=
      if t < 20 then ((b &&& c) ||| (~~~b &&& d), (0x5A827999 : UInt32))
      else if t < 40 then (b ^^^ c ^^^ d, 0x6ED9EBA1)
      else if t < 60 then ((b &&& c) ||| (b &&& d) ||| (c &&& d), 0x8F1BBCDC)
      else (b ^^^ c ^^^ d, 0xCA62C1D6)
    let temp := rotl a 5 + f + e + k + w[t]
    e := d
    d := c
    c := rotl b 30
    b := a
    a := temp
  return #v[state[0] + a, state[1] + b, state[2] + c, state[3] + d, state[4] + e]

def absorb (state : State) (bytes : ByteArray) : State := Id.run do
  let mut s := state
  for h : k in [0:bytes.size / 64] do
    have : k < bytes.size / 64 := h.upper
    s := compress s (Sha256.blockAt bytes (64 * k) (by omega))
  return s

def State.bytes (state : State) : ByteArray :=
  ⟨(state.toArray.map fun (w : UInt32) =>
    #[(w >>> 24).toUInt8, (w >>> 16).toUInt8, (w >>> 8).toUInt8, w.toUInt8]).flatten⟩

def hash (msg : ByteArray) : ByteArray :=
  (absorb initial (msg ++ Sha256.padding msg.size)).bytes

end Lanes.Sha1
