/-
Copyright (c) 2026 The Lanes Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Lanes
public import Lanes.Check.FingerprintSound
public import Lanes.Check.ReduceSound
public import Lanes.Check.SearchSound
public import Lanes.Check.SystemSound
public import Lanes.Db.Sound
public import Lanes.Db.JobsSound
public import Lanes.Db.OnceSound
public import Lanes.Db.WorkerSound
public import Lanes.Lib.Encoding.Json.BasicSound
public import Lanes.Lib.Encoding.Json.ParserSound
public import Lanes.Lib.Encoding.Json.PrinterSound
public import Lanes.Lib.Mime.MediaTypeSound
public import Lanes.Lib.Net.UrlSound
public import Lanes.Outside.Store.Sound
public import Lanes.Proof.JoinSound
public import Lanes.Proof.MapIOSound
public import Lanes.Runtime.KernelSound
public import Lanes.Runtime.KernelTimers
public import Lanes.Runtime.SchedSound
public import Lanes.Web.Auth.RowsSound
public import Lanes.Web.Auth.TokenSound
public import Lanes.Web.Html.BasicSound
public import Lanes.Web.Html.HtmxSound
public import Lanes.Web.Http.AdmitSound
public import Lanes.Web.Http.ConnSound
public import Lanes.Web.Http.CookieSound
public import Lanes.Web.Http.FrontSound
public import Lanes.Web.Http.OpsSound
public import Lanes.Web.Http.ReadRequestSound
public import Lanes.Web.Http.RouteSound
public import Lanes.Web.Http.SseSound
public import Lanes.Web.Http.SigV4Sound
public import Lanes.Web.Http.WireSound

/-!
The framework's soundness theorems: what the kernel, the shell, joins, the checker, the HTTP
reader and server, HTML, tokens, JSON, URLs and media types are proved to do. `import Lanes`
leaves them out so that an application builds and imports less; a proof that cites one imports
this, and `Lanes.Semantics` imports it. It imports only `Std`. The services' soundness theorems
are imported by `Lanes.Services`.
-/
