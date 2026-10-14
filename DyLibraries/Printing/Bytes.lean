module

public import DyLibraries.Printing.Basic
public import DyExtensions.Actions.Random
public import DY.EquationalTheory.Literal
public import DY.EquationalTheory.Concat
public import DyExtensions.EquationalTheory.PublicKeyEncryption
public import DY.EquationalTheory.Sign
public import DyExtensions.EquationalTheory.AEAD
public import DY.EquationalTheory.Hash
public import DY.EquationalTheory.DiffieHellman
public import DY.EquationalTheory.KdfExtract
public import DY.EquationalTheory.KdfExpand

namespace DY.Printing

/-- Printable ASCII is quoted; other bytes use lossless hexadecimal escapes. -/
public def literalToString (bytes : ByteArray) : String := Id.run do
  let mut parts : Array String := #["\""]
  for b in bytes do
    let n := b.toNat
    let part := if n == 34 then "\\\"" else if n == 92 then "\\\\" else if 32 ≤ n && n ≤ 126 then String.singleton (Char.ofNat n) else "\\x" ++ String.singleton ("0123456789abcdef".toList[n / 16]!) ++ String.singleton ("0123456789abcdef".toList[n % 16]!)
    parts := parts.push part
  return String.join (parts.push "\"").toList

end DY.Printing

namespace DY
open Printing

namespace Literal.Literal
public def SubF.printing [BytesFunctor] : PartialBytesPrinter SubF := fun {lit := lit} _ => literalToString lit
end Literal.Literal

namespace Random
public def SubF.printing [BytesFunctor] : PartialBytesPrinter SubF := fun {timestamp, ..} _ => s!"Nonce #{timestamp}"
end Random

namespace Concat.Concat
public def SubF.printing [BytesFunctor] : PartialBytesPrinter SubF := fun {lhs, rhs} rec => s!"[{rec lhs},{rec rhs}]"
end Concat.Concat

namespace PublicKeyEncryption.Pk
public def SubF.printing [BytesFunctor] : PartialBytesPrinter SubF := fun {sk := sk} rec => s!"Pk(sk=({rec sk}))"
end PublicKeyEncryption.Pk

namespace PublicKeyEncryption.Ciphertext
public def SubF.printing [BytesFunctor] : PartialBytesPrinter SubF := fun {publicKey, nonce, message} rec => s!"PkeEnc(pk=({rec publicKey}), nonce=({rec nonce}), msg=({rec message}))"
end PublicKeyEncryption.Ciphertext

namespace Signature.Vk
public def SubF.printing [BytesFunctor] : PartialBytesPrinter SubF := fun {sk := sk} rec => s!"Vk({rec sk})"
end Signature.Vk

namespace Signature.Sign
public def SubF.printing [BytesFunctor] : PartialBytesPrinter SubF := fun {sk, nonce, msg} rec => s!"sig(sk=({rec sk}), nonce=({rec nonce}), msg=({rec msg}))"
end Signature.Sign

namespace AEAD.Ciphertext
public def SubF.printing [BytesFunctor] : PartialBytesPrinter SubF := fun {key, nonce, message, associatedData} rec => s!"AeadEnc(key=({rec key}), nonce=({rec nonce}), msg=({rec message}), ad=({rec associatedData}))"
end AEAD.Ciphertext

namespace Hash.Hash
public def SubF.printing [BytesFunctor] : PartialBytesPrinter SubF := fun {input := input} rec => s!"Hash({rec input})"
end Hash.Hash

namespace DiffieHellman.DhPk
public def SubF.printing [BytesFunctor] : PartialBytesPrinter SubF := fun {sk := sk} rec => s!"DhPub(sk=({rec sk}))"
end DiffieHellman.DhPk

namespace DiffieHellman.Dh
public def SubF.printing [BytesFunctor] : PartialBytesPrinter SubF := fun {pk, sk} rec => s!"Dh(sk=({rec sk}), pk=({rec pk}))"
end DiffieHellman.Dh

namespace KdfExtract.KdfExtract
public def SubF.printing [BytesFunctor] : PartialBytesPrinter SubF := fun {salt, ikm} rec => s!"KdfExtract(salt=({rec salt}), ikm=({rec ikm}))"
end KdfExtract.KdfExtract

namespace KdfExpand.KdfExpand
public def SubF.printing [BytesFunctor] : PartialBytesPrinter SubF := fun {prk, info, len} rec => s!"KdfExpand(prk=({rec prk}), info=({rec info}), len={len})"
end KdfExpand.KdfExpand

namespace Literal
#combine into BytesPrinter from Literal
end Literal

namespace Concat
#combine into BytesPrinter from Concat
end Concat

namespace PublicKeyEncryption
/-- Customize ciphertext rendering while retaining the standard public-key printer. -/
public def SubF.printing [BytesFunctor] (ciphertextPrinter : PartialBytesPrinter Ciphertext.SubF := Ciphertext.SubF.printing) : PartialBytesPrinter SubF := Bytes.PartialFunction.combine fun
  | 0 => Pk.SubF.printing
  | 1 => ciphertextPrinter
end PublicKeyEncryption

namespace Signature
/-- Customize signature rendering while retaining the standard verification-key printer. -/
public def SubF.printing [BytesFunctor] (signaturePrinter : PartialBytesPrinter Sign.SubF := Sign.SubF.printing) : PartialBytesPrinter SubF := Bytes.PartialFunction.combine fun
  | 0 => Vk.SubF.printing
  | 1 => signaturePrinter
end Signature

namespace AEAD
/-- Customize ciphertext rendering, defaulting to the standard symbolic printer. -/
public def SubF.printing [BytesFunctor] (ciphertextPrinter : PartialBytesPrinter Ciphertext.SubF := Ciphertext.SubF.printing) : PartialBytesPrinter SubF := Bytes.PartialFunction.combine fun
  | 0 => ciphertextPrinter
end AEAD

namespace Hash
#combine into BytesPrinter from Hash
end Hash

namespace DiffieHellman
#combine into BytesPrinter from DhPk, Dh
end DiffieHellman

namespace KdfExtract
#combine into BytesPrinter from KdfExtract
end KdfExtract

namespace KdfExpand
#combine into BytesPrinter from KdfExpand
end KdfExpand

end DY
