//Aim: Try to find BkAyToLyOpt
type BkTy = PrmBk | SwBk | SqBk | RmkBk | ErBk
type Bk = {ty:BkTy;ly:string[]}
let BkTy(b:Bk)=b.ty
let BkLy(b:Bk)=b.ly
let optVal(a:'a option) = a.Value
let optMap f (a:'a option) = if(a.IsSome) then Some(f a.Value) else None
let ayFindOpt = Array.tryFind
let eq a b = a = b
//let BkAyToLyOpt ty = BkTy >> eq ty |> ayFindOpt >> optMap BkLy
let BkAyToLyOpt ty b =
    let b' = b |> ayFindOpt (BkTy >> eq ty)
    if b'.IsSome then Some(b'.Value.ly) else None
let BkAy = 
    [|
        {ty=PrmBk;ly=[|"a";"b"|]}
        {ty=SwBk;ly=[|"a";"b"|]}
        {ty=PrmBk;ly=[|"a";"b"|]}
    |]
let lyOpt = BkAyToLyOpt PrmBk BkAy
lyOpt
