#nowarn "40" 
#nowarn "64" 
namespace Lib.ChkLy
open Lib.Core
module ZTyp =
    type IxLin = { ix: int; lin: string }
    type IxMsg = { ix: int; msg: string }
open ZTyp
module IxMsg =
    let make(ix,msg) = {ix=ix;msg=msg}
    let put ly (ixMsg:IxMsg list) : string =
        let ixEq ix {ix=ix';msg=_} = ix = ix'
        let msg {ix=_;msg=msg} = msg
        let pickMsg ( ix  : int )
                    ( lis : IxMsg list ) : string list =
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
            lin |> List.toArray |> jnSyCrLf
        let map1 (ix,lin):string*string list = 
            let msgLis = pickMsg ix ixMsg
            lin,msgLis
        if List.isEmpty ixMsg then ly|>jnSyCrLf else
            ly |> syAlignL
               |> ayAddIx
               |> Array.map map1 
               |> Array.map map2
               |> jnSyCrLf
module ChkLinFun =
    let apply ixlisLinlis f = 
        let ixlis,linlis = ixlisLinlis
        linlis |> List.map f
               |> OptLis.zip ixlis
               |> List.map IxMsg.make
module ChkBkFun =
    let apply ( ixlisLinlis : int list * string list       )
              ( f           : string list -> string[] list ) : IxMsg list = 
        let ixlis,linlis = ixlisLinlis
        let withMsg(_,msg:string[]) = Array.isEmpty msg |> not
        let expand(ix,msg:string[]):IxMsg list = 
            msg |> Array.map (fun msg-> {ix=ix;msg=msg}) 
                |> ayToLis
        let a = linlis |> f
        let b = List.zip ixlis a
        let c = b |> lisWh withMsg
        let d = c |> lisMap expand |> List.concat
        d 
module IxLin =
    let skip   ( skiplinFun':(string->bool) option)
               ( ly                               ) : int list*string list =
        let p(_,lin) = if skiplinFun'.IsNone then true else (skiplinFun'.Value lin)
        ly |> Array.toList 
           |> lisAddIx 
           |> List.where p 
           |> List.unzip

    let chklin ( flis        : (string -> string option) list)
               ( ixlisLinlis : int list * string list        ) : IxMsg list = 
        flis |> List.map (ChkLinFun.apply ixlisLinlis) 
             |> List.concat 

    let chkbk  ( flis        : (string list->string[] list) list ) 
               ( ixlisLinlis : int list * string list            ) : IxMsg list = 
        flis |> List.map (ChkBkFun.apply ixlisLinlis)
             |> List.concat

    let chkT1Dup ( ixlisLinlis : int list * string list ) : IxMsg list = 
        chkbk [dupFstTermMsgAyLis] ixlisLinlis
module Ly =
    let chk(chklinFunlis  : (string      -> string option) list ) 
           (chkbkFunlis   : (string list -> string[] list) list )
           (chkTermOneDup : bool                                )
           (skipLinFun'   : (string->bool) option               )
           (ly            : string[]                            ) : bool*string =
        let ly' = IxLin.skip skipLinFun' ly
        let r1 = ly' |> IxLin.chklin chklinFunlis
        let r2 = ly' |> IxLin.chkbk  chkbkFunlis
        let r3 = if chkTermOneDup then ly' |> IxLin.chkT1Dup else []
        let r = r1@r2@r3
        let newTp = IxMsg.put ly r
        let clnTp = ly |> syRmv3DashRmk |> syRmvEmpLin |> jnSyCrLf
        let isEr = List.isEmpty r |> not
        isEr,newTp
module Tp =
    let chk(chklinFunlis  : (string      -> string option) list ) 
           (chkbkFunlis   : (string list -> string[] list) list )
           (chkTermOneDup : bool                                )
           (skipLinFun'   : (string->bool) option               )
           (tp            : string                              ) : bool*string =
        Ly.chk(chklinFunlis)(chkbkFunlis)(chkTermOneDup)(skipLinFun')(splitCrLf tp)
    let tst() =
        let linF0 lin = Some lin
        let bkF0 linlis = linlis |> List.map (fun lin -> [|lin;lin|])
        let bkFlis = [bkF0]
        let linFlis = [linF0]
        let tp = """klsdjflksdjf
aa sldkfjsfd
bb sdfjlsdfk
bb sldkfjsdlfksdf
cc sdlkfdsfkldf"""
        chk linFlis bkFlis true None tp
[<AutoOpen>]
module AutoOpen =
    let tpChk = Tp.chk
    let lyChk = Ly.chk
        