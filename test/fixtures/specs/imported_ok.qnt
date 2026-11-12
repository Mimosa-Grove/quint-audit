// imported-source fixture for the decoder mirror.
//
// This file is longer than the main clean fixture on purpose: the module
// span in the mirror fixture points at the closing brace below, whose byte
// offset is past the main file's length. A decoder that measures every span
// against the main file refuses it; the contract decodes it against this
// file.
//
// The file is ASCII and carries no mapped IR of its own. It is source text
// only, used to give the imported source index a resolvable path and a
// length.
//
// padding padding padding padding padding padding padding padding padding
// padding padding padding padding padding padding padding padding padding
// padding padding padding padding padding padding padding padding padding
// padding padding padding padding padding padding padding padding padding
// padding padding padding padding padding padding padding padding padding
// padding padding padding padding padding padding padding padding padding
// padding padding padding padding padding padding padding padding padding
// padding padding padding padding padding padding padding padding padding
// padding padding padding padding padding padding padding padding padding
// padding padding padding padding padding padding padding padding padding
// padding padding padding padding padding padding padding padding padding
module ImportedOk {
  var y: int
}
