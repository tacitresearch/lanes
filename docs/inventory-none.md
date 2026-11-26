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

## Specs reached through a definition of another module

`Once.server_implements` and `Examples.KV.implements_once` are stated with
`System.ImplementsOnce`, which unfolds to these; the inventory follows a statement's definitions
only within their own module, so it does not see that the theorems state them.

### `Lanes/Semantics/Once.lean`

- `Service.Once.take`
- `Service.once`

## Without evidence on the day the inventory was introduced (2026-11-26)

Each is to be proved, tested, made private or removed.

### `Lanes/Actors/Actor.lean`

- `Actor.mapEff`
- `Actor.comapMsg`

### `Lanes/Actors/CourierSound.lean`

- `Peers.Line.conn?`

### `Lanes/Actors/Equiv.lean`

- `onLink`

### `Lanes/Actors/Inspect.lean`

- `instReprEmpty_lanes`
- `Event.kind`
- `Event.kinds`
- `Slot.same`
- `Slot.allSame`
- `Slot.hash`
- `SysState.render`

### `Lanes/Actors/Outside.lean`

- `Outside.any`

### `Lanes/Actors/Run.lean`

- `Effect.sends`
- `Effect.armed`
- `Effect.emits`

### `Lanes/Actors/Service.lean`

- `Service.start`
- `Service.State.call`
- `Service.apply`
- `Service.State.fire`
- `Service.State.ret`

### `Lanes/Actors/Snapshot.lean`

- `Journal.saved?`

### `Lanes/Actors/System.lean`

- `Effect.isStop`
- `Envelope.sameLink`
- `EnvModel.distributed`

### `Lanes/Auth/Login.lean`

- `Auth.instHashableDigest`
- `Auth.instReprDigest`
- `Auth.Attempts.unlock`

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

### `Lanes/Data/Frame.lean`

- `Frame.unfinished`

### `Lanes/Data/Json/Basic.lean`

- `JsonNumber.instCoeNat`
- `JsonNumber.instCoeInt`
- `JsonNumber.instInhabited`
- `JsonNumber.instToString`
- `Json.instCoeNat`
- `Json.instCoeInt`
- `Json.instCoeString`
- `Json.instCoeBool`

### `Lanes/Data/Json/Printer.lean`

- `Json.instToString`

### `Lanes/Html/Basic.lean`

- `Html.empty`
- `Html.instInhabited`
- `instToHtmlArray`
- `instToHtmlOption`
- `instToAttrInt`
- `instToAttrOption`

### `Lanes/Html/Htmx.lean`

- `Hx.confirm`
- `Hx.boost`
- `Hx.pushUrl`
- `Hx.indicator`
- `Http.Request.isHtmx`
- `Http.Response.hxRedirect`

### `Lanes/Http/Basic.lean`

- `Http.Request.param?`
- `Http.Request.header?`
- `Http.Response.json`
- `Http.Response.redirect`
- `Http.Response.withHeader`

### `Lanes/Http/Cookie.lean`

- `Http.Request.bodyWithin`
- `Http.Response.noStore`

### `Lanes/Http/Front.lean`

- `Http.servedActors`

### `Lanes/Http/Gate.lean`

- `Http.instReprGateMsgOfOut`

### `Lanes/Http/Route.lean`

- `Http.Slug.instToString`
- `Http.Path.append`
- `Http.Route.put`
- `Http.Route.patch`
- `Http.Route.delete`

### `Lanes/Semantics/Liveness.lean`

- `System.Run.idle`
