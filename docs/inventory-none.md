# Definitions without evidence

The definitions of `Lanes/` whose status in `docs/INVENTORY.md` is none. `lanes lint` fails on
one that is not here, and on an entry here that has evidence now or no longer exists, so the list
only shrinks. Each entry is under a heading that says why it is here; a new one needs a heading
of its own. The rules are in `docs/decisions/D47-the-inventory-is-computed.md`.

## Helpers of `lanes_data`, run by the compiler: a test uses the command, not them

What they write is checked by Lean like any declaration, and the laws of a codec and of an
enumeration are fields of its type. That the declaration is the one written is what
`Tests/Codec.lean` tests, through the command, which names no constant.

- `Declare.params`
- `Declare.classBinders`
- `Declare.productType`
- `Declare.sumType`
- `Declare.splitDeriving`
- `Declare.leanDeriving`
- `Declare.codable`
- `Declare.conjunction`
- `Declare.fieldwise`
- `Declare.comparedByBEq`
- `Declare.independent`
- `Declare.enum`
- `Declare.migrate`

## Without evidence on the day the inventory was introduced (2026-11-26)

Each is to be proved, tested, made private or removed.

### `Lanes/Core/Actor.lean`

- `Actor.mapEff`

### `Lanes/Net/CourierSound.lean`

- `Peers.Line.conn?`

### `Lanes/Proof/Equiv.lean`

- `onLink`

### `Lanes/Core/Inspect.lean`

- `Event.kind`
- `Event.kinds`
- `Slot.same`
- `Slot.allSame`
- `Slot.hash`
- `SysState.render`

### `Lanes/Core/Run.lean`

- `Effect.armed`

### `Lanes/Core/Service.lean`

- `Service.start`
- `Service.State.call`
- `Service.apply`
- `Service.State.fire`
- `Service.State.ret`

### `Lanes/Core/System.lean`

- `EnvModel.distributed`

### `Lanes/Check/Fuzz.lean`

- `Check.FuzzReport.render`

### `Lanes/Check/SystemSound.lean`

- `Event.isInternal`

### `Lanes/Data/Codec.lean`

- `Codec.fresh`
- `Codec.tuple`
- `Codec.product`
- `Codec.inject`

### `Lanes/Data/Fifo.lean`

- `Fifo.push`
- `Fifo.pop?`
- `Fifo.filter`

### `Lanes/Durable/Frame.lean`

- `Frame.unfinished`

### `Lanes/Lib/Encoding/Json/Basic.lean`

- `JsonNumber.instCoeNat`
- `JsonNumber.instCoeInt`
- `JsonNumber.instInhabited`
- `JsonNumber.instToString`
- `Json.instCoeNat`
- `Json.instCoeInt`
- `Json.instCoeString`
- `Json.instCoeBool`

### `Lanes/Lib/Encoding/Json/Printer.lean`

- `Json.instToString`

### `Lanes/Web/Http/Front.lean`

- `Http.servedActors`

### `Lanes/Web/Http/Gate.lean`

- `Http.instReprGateMsgOfOut`

### `Lanes/Semantics/Liveness.lean`

- `System.Run.idle`
