/-
Copyright (c) 2026 The Lanes Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Lanes
public import Lanes.Behaviours.Jobs.Sound
public import Lanes.Behaviours.Schedule.Sound
public import Lanes.Check.SearchSound
public import Lanes.Check.SystemSound
public import Lanes.Lib.Encoding.Json.BasicSound
public import Lanes.Lib.Encoding.Json.ParserSound
public import Lanes.Lib.Encoding.Json.PrinterSound
public import Lanes.Lib.Mime.MediaTypeSound
public import Lanes.Lib.Net.UrlSound
public import Lanes.Lib.Postgres.ConnSound
public import Lanes.Lib.Postgres.MessageSound
public import Lanes.Net.CourierSound
public import Lanes.Outside.Store.Sound
public import Lanes.Proof.JoinSound
public import Lanes.Proof.MapIOSound
public import Lanes.Runtime.KernelSound
public import Lanes.Runtime.KernelTimers
public import Lanes.Runtime.MailboxSound
public import Lanes.Runtime.ShardSound
public import Lanes.Runtime.ShardsSound
public import Lanes.Web.Auth.TokenSound
public import Lanes.Web.Html.BasicSound
public import Lanes.Web.Html.HtmxSound
public import Lanes.Web.Http.ConnSound
public import Lanes.Web.Http.CookieSound
public import Lanes.Web.Http.FrontSound
public import Lanes.Web.Http.OpsSound
public import Lanes.Web.Http.ReadRequestSound
public import Lanes.Web.Http.RouteSound
public import Lanes.Web.Http.SseSound
public import Lanes.Web.Http.SigV4Sound
public import Lanes.Web.Http.WireSound
public import Lanes.Web.S3.PostSound

/-!
The framework's soundness theorems: what the kernel, the shell, joins, shards, the transport,
the checker, the HTTP reader and server, PostgreSQL's messages and connection, HTML, tokens, JSON, URLs and media types are proved to
do. `import Lanes` leaves them out so that an application builds and imports less; a proof that
cites one imports this, and `Lanes.Semantics` imports it. It imports only `Std`.
-/
