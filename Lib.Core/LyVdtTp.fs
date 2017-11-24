namespace Lib.LyVdt
open Lib.Core
type msgs = msg list
type linMsgs = lin*msgs
type endMsgs = msgs
type chkFstTermDup = bool
type tp = lines
type msgLy = ly
type linWdt = wdt
type msgTp = tp
type vdtTp = isEr * msgTp
type lyMsgs = msgs[]
type vdtMsgs = lyMsgs*endMsgs
type chkr = ly -> vdtMsgs
type LyMsgs(lyMsgs:lyMsgs) =
    let zLinCnt = sz lyMsgs
    let zIsEmpty = zLinCnt = 0 || (lyMsgs |> ayAny lisIsEmpty)
    member x.linCnt = zLinCnt
    member x.isEmpty = zIsEmpty
    member x.lyMsgs = lyMsgs
    static member empty:LyMsgs = LyMsgs([||])
    static member (+)(a:LyMsgs,b:LyMsgs):LyMsgs =
        if a.linCnt <> b.linCnt then er "{sz1} <> {sz2}, cannot add" [a.linCnt;b.linCnt]
        let lyMsgs = a.lyMsgs |> ayZip b.lyMsgs |> ayMap (fun(a:msgs,b:msgs)->a@b)
        LyMsgs(lyMsgs)
module LinMsgs =
    let lines(w:linWdt)(linMsgs:linMsgs):lines = 
        let lin,msgs = linMsgs
        if lisIsEmpty msgs then lin else
            let lin0 = 
                let msg0 = List.head msgs
                ( alignL w lin ) + msg0
            let linRst = 
                let linesRst = List.tail msgs |> jnCrLf
                linesTab "" w linesRst
            let o = lin0 + linRst
            o
type VdtMsgs(vdtMsgs:vdtMsgs) =
    inherit LyMsgs(fst vdtMsgs)
    let zLyMsgs,zEndMsgs = vdtMsgs
    let zIsEmpty = base.isEmpty && lisIsEmpty zEndMsgs
    let zIsEr = not(base.isEmpty || (lisIsEmpty zEndMsgs))
    static member (+)(a:VdtMsgs,b:VdtMsgs):VdtMsgs =
        let lm1,em1 = a.vdtMsgs
        let lm2,em2 = b.vdtMsgs
        let lm,em = 
            match a.isEmpty , b.isEmpty with
            | true,_ -> lm2,em2
            | _,true -> lm1,em1
            | _,_ ->
                let lm = ((a:>LyMsgs) + (b:>LyMsgs)).lyMsgs
                let em = em1 @ em2
                lm,em
        VdtMsgs(lm,em)
    static member empty:VdtMsgs = VdtMsgs(VdtMsgs.empVdtMsgs)
    static member empVdtMsgs:vdtMsgs = [||],[]
    member x.vdtMsgs = vdtMsgs
    member x.vdtTp fstLinOpt (ly:ly): vdtTp = 
        let fstLin = if isSome fstLinOpt then fstLinOpt.Value + "\r\n" else ""
        let msgTp = fstLin + x.lines ly 
        let vdtTp = zIsEr,msgTp
        vdtTp
    member x.msgsTp(ly):msgTp =
        let w = ssWdt ly
        let toLines(msgs:msgs,lin) = 
            if lisIsEmpty msgs then lin else
                let lin0 = 
                    let msg0 = List.head msgs
                    ( alignL w lin ) + msg0
                let linRst = 
                    let linesRst = List.tail msgs |> jnCrLf
                    linesTab "" w linesRst
                let o = lin0 + linRst
                o
        let msgTp = (ly|>ayZip zLyMsgs|> ayMap toLines|>ayToLis)@zEndMsgs|>jnCrLf
        msgTp
    member x.isEr = zIsEr
    member x.isEmpty = zIsEmpty
    member x.lines(ly:ly):lines =
        if zIsEmpty then ly |> jnCrLf else
            let linMsgsAy:linMsgs[] = ayZip ly zLyMsgs
            let w = ssWdt ly + 1
            let lines = linMsgsAy|>ayMap(LinMsgs.lines w) |>jnCrLf
            let endLines = zEndMsgs |> lisToAy |> syAddPfx "--- " |> jnCrLf
            let lines = if endLines="" then lines else lines+"\r\n"+endLines
            lines
module Chkr =
    let empty:chkr = fun(ly:ly)->VdtMsgs.empty.vdtMsgs
    let dupFstTermChkr:ly->vdtMsgs=fun(ly:ly)->(ly|>ly_dupFstTermLyMsgs),[]
module Ly =
    let vdtMsgs(chkrLis:chkr list)(chkFstTerm:chkFstTermDup)(ly:ly):vdtMsgs =
        let clnLy = ly|>ly_rmv3DashRmk|>syRTrim 
        let apply(chkr:chkr):VdtMsgs=VdtMsgs(chkr clnLy)
        let l =
            if chkFstTerm then 
                let mkChkr:chkr=fun(ly:ly)->(ly|>ly_dupFstTermLyMsgs),[]
                mkChkr::chkrLis
            else
                chkrLis
        let vm = 
            let add a b = VdtMsgs.(+)(a,b)
            l |> lisMap apply |> lisFold add (VdtMsgs.empty)
        vm.vdtMsgs
