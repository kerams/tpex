namespace FSharp.TpEx

type GenerateStringer (_type: System.Type) =
    inherit System.Attribute ()

[<assembly: CompilerServices.TypeProviderAssembly("FSharp.TpEx")>]
do ()
