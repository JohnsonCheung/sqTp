#nowarn "40" 
#nowarn "64" 
namespace Lib.ChkLy
open Lib.Core
module ZTyp =
    type ixLin = { ix: int; lin: string }
    type ixMsg = { ix: int; msg: string }
    type linChkr = string -> string option
    type bkChkr = string[] -> string list[]
    type linPred = string -> bool
    type ixAyLy = int[] * string[]
open ZTyp
module internal IxMsg =
    let make(ix,msg) = {ix=ix;msg=msg}
    let put ly (ixMsg:ixMsg list) : string =
        let ixEq ix {ix=ix';msg=_} = ix = ix'
        let msg {ix=_;msg=msg} = msg
        let pickMsg ( ix  : int )
                    ( lis : ixMsg list ) : string list =
                    lis |> List.where (ixEq ix)
                        |> List.map msg
        let map2(lin,msgLis:string list) =
            let h = msgLis |> List.tryHead 
            let msg0 = h |> Opt.dft ""
            let msg0 = if msg0="" then "" else "--- " + msg0
            let lin0 = lin + " " + msg0
            let s = spc ((len lin) + 1) + "--- "
            let linRst = 
                if (List.length msgLis <= 1) then [] else
                    msgLis |> List.skip 1 |> List.map (addPfx s)
            let lin = lin0::linRst
            lin |> List.toArray |> jnCrLf
        let map1 (ix,lin):string*string list = 
            let msgLis = pickMsg ix ixMsg
            lin,msgLis
        if List.isEmpty ixMsg then ly|>jnCrLf else
            ly |> syAlignL
               |> ayAddIx
               |> Array.map map1 
               |> Array.map map2
               |> jnCrLf
module internal ChkLinFun =
    let apply ixAyLy (f:linChkr) : ixMsg list = 
        let ixAy,ly = ixAyLy
        ly |> ayMap f |> OptAy.zip ixAy |> ayMap(IxMsg.make) |> ayToLis
module internal ChkBkFun =
    let apply ( ixAyLy : ixAyLy )
              ( f      : bkChkr ) : ixMsg list = 
        let ixAy,ly = ixAyLy
        let withMsg(_,msgLis) = List.isEmpty msgLis |> not
        let expand(ix,msgLis) = msgLis |> lisMap (fun msg-> {ix=ix;msg=msg}) 
        let a = ly |> f             // string list []         
        let b = Array.zip ixAy a    // (int * string list) [] 
        let c = b |> ayWh withMsg   // (int * string list) [] 
        let d = c |> ayMap expand   // (ixMsg list) []        
        let e = d |> List.concat
        e
    let ofChkDup = syFstTermDupMsg >> ayMap optToLisOfOneEle
module internal IxLin =
    let skip   ( skiplinFunOpt:linPred option)
               ( ly                        ) : int[]*string[] =
        let p(_,lin) = if skiplinFunOpt.IsNone then true else (skiplinFunOpt.Value lin |> not)
        ly |> ayAddIx
           |> ayWh p 
           |> Array.unzip
    let chklin(flis:linChkr list)(ixAyLy:ixAyLy):ixMsg list =
        flis |> lisMap (ChkLinFun.apply ixAyLy) |> List.concat
    let chkbk  ( flis   : bkChkr list ) 
               ( ixAyLy : ixAyLy        ) : ixMsg list = 
        flis |> lisMap(ChkBkFun.apply ixAyLy) |> List.concat
    let chkT1Dup ( ixAyLy : ixAyLy) : ixMsg list = 
        chkbk [ChkBkFun.ofChkDup] ixAyLy
module internal Ly =
    let chk(linChkrLis:linChkr list)(bkChkrLis:bkChkr list)(chkTermOneDup:bool)(skipLinFunOpt:linPred option)(ly:string[]) : bool*string =
        if ayFstEleOpt ly=Some "?LvlY    EQ %SumLvl Y" then
            ()
        else
            ()
        let ly' = IxLin.skip skipLinFunOpt ly
        let r1 = ly' |> IxLin.chklin linChkrLis
        let r2 = ly' |> IxLin.chkbk bkChkrLis
        let r3 = if chkTermOneDup then ly' |> IxLin.chkT1Dup else []
        let r = r1 @ r2 @ r3
        let newTp = IxMsg.put ly r
        let clnTp = ly |> syRmv3DashRmk |> syRmvEmpLin |> jnCrLf
        let isEr = List.isEmpty r |> not
        isEr,newTp
module internal Tp =
    let chk(chklinLis  : linChkr list )
           (chkbkLis   : bkChkr list  )
           (chkTermOneDup : bool           )
           (skipLinFun'   : linPred option )
           (tp            : string         ) : bool*string =
        Ly.chk(chklinLis)(chkbkLis)(chkTermOneDup)(skipLinFun')(splitCrLf tp)
    let tst() =
        let linF0 lin = Some lin
        let bkF0 ly = 
            let o  =ly |> Array.map (fun lin -> [lin;lin])
            if Array.length ly <> Array.length o then failwith "stop"
            o
        let bkFlis = [bkF0]
        let linFlis = [linF0]
        let tp = """klsdjflksdjf
aa sldkfjsfd
bb sdfjlsdfk
bb sldkfjsdlfksdf
cc sdlkfdsfkldf"""
        chk linFlis bkFlis true None tp
[<AutoOpen>]
module ChkLy =
    let tpChk = Tp.chk
    let lyChk = Ly.chk
    let tst = Tp.tst
        