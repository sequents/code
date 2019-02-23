module Binary 

import public Control.IOExcept
import public Control.Catchable
import Data.Buffer
import Data.List

-- stolen from https://github.com/edwinb/Blodwen/blob/master/src/Utils/Binary.idr

export
record Chunk where
  constructor MkChunk
  buf : Buffer
  loc : Int
  size : Int -- Capacity
  used : Int -- Amount used

newChunk : Buffer -> Chunk
newChunk b = MkChunk b 0 (size b) 0

avail : Chunk -> Int
avail c = size c - loc c

toRead : Chunk -> Int
toRead c = used c - loc c

appended : Int -> Chunk -> Chunk
appended i c = record { loc $= (+i),
                        used $= (+i) } c

incLoc : Int -> Chunk -> Chunk
incLoc i c = record { loc $= (+i) } c

-- Serialised data is stored as a list of chunks, in a zipper.
-- i.e. processed chunks, chunk we're working on, chunks to do
export
data Binary = MkBin (List Chunk) Chunk (List Chunk)

export 
dumpChunk : Chunk -> IO ()
dumpChunk (MkChunk buf loc size used) = 
  do dt <- bufferData buf
     printLn dt
     printLn loc
     printLn size
     printLn used

export
dumpBin : Binary -> IO ()
dumpBin (MkBin done chunk rest)
   = do traverse dumpChunk done
        dumpChunk chunk
        traverse dumpChunk rest
        pure ()

nonEmptyRev : NonEmpty (xs ++ y :: ys)
nonEmptyRev {xs = []} = IsNonEmpty
nonEmptyRev {xs = (x :: xs)} = IsNonEmpty

reset : Binary -> Binary
reset (MkBin done cur rest) 
    = setBin (reverse done ++ cur :: rest) nonEmptyRev
  where
    setBin : (xs : List Chunk) -> (prf : NonEmpty xs) -> Binary
    setBin (chunk :: rest) IsNonEmpty 
        = MkBin [] (record { loc = 0 } chunk)
                   (map (record { loc = 0 }) rest)

req : List Chunk -> Int
req [] = 0
req (c::cs) = used c + req cs

-- Take all the data from the chunks in a 'Binary' and copy them into one
-- single buffer, ready for writing to disk.
-- TODO: YAGNI? Delete if so...
toBuffer : Binary -> IO (Maybe Buffer)
toBuffer (MkBin done cur rest)
    = do let chunks = reverse done ++ cur :: rest
         Just b <- newBuffer (req chunks)
              | Nothing => pure Nothing
         copyToBuf 0 b chunks
         pure (Just b)
  where
    copyToBuf : (pos : Int) -> Buffer -> List Chunk -> IO ()
    copyToBuf pos b [] = pure ()
    copyToBuf pos b (c :: cs)
        = do copyData (buf c) 0 (used c) b pos
             copyToBuf (pos + used c) b cs

fromBuffer : Buffer -> IO Binary
fromBuffer buf
    = do len <- rawSize buf
         pure (MkBin [] (MkChunk buf 0 len len) []) -- assume all used

export
writeToFile : (fname : String) -> Binary -> IO (Either FileError ())
writeToFile fname (MkBin done cur rest)
    = do Right h <- openFile fname WriteTruncate
               | Left err => pure (Left err)
         let chunks = reverse done ++ cur :: rest
         writeChunks h chunks
         closeFile h
         pure (Right ())
  where
    writeChunks : File -> List Chunk -> IO ()
    writeChunks h [] = pure ()
    writeChunks h (c :: cs)
        = do writeBufferToFile h (resetBuffer (buf c)) (used c)
             writeChunks h cs

export
readFromFile : (fname : String) -> IO (Either FileError Binary)
readFromFile fname
    = do Right h <- openFile fname Read
               | Left err => pure (Left err)
         Right max <- fileSize h
               | Left err => pure (Left err)
         Just b <- newBuffer max
               | Nothing => pure (Left $ GenericFileError 0) --- um, not really
         b <- readBufferFromFile h b max
         pure $ Right $ MkBin [] (MkChunk b 0 max max) []

public export
IOE : Type -> Type 
IOE = IOExcept String

-- Create a new list of chunks, initialised with one 64k chunk
export
initBinary : IOE Binary
initBinary
    = do Just buf <- ioe_lift $ newBuffer 65536
             | Nothing => throw "Buffer creation failed"
         pure $ MkBin [] (newChunk buf) []

public export
interface Codec a where 
  toBuf : Binary -> a -> IOE Binary
  fromBuf : Binary -> IOE (a, Binary)

export
Codec Bits8 where
  toBuf (MkBin done chunk rest) val = 
         if avail chunk >= 1
            then
              do ioe_lift $ setByte (buf chunk) (loc chunk) val
                 pure $ MkBin done (appended 1 chunk) rest
            else 
              do Just newbuf <- ioe_lift $ newBuffer 65536
                    | Nothing => throw "Buffer expansion failed"
                 ioe_lift $ setByte newbuf 0 val
                 pure $ MkBin (chunk :: done)
                              (MkChunk newbuf 1 (size newbuf) 1)
                              rest

  fromBuf (MkBin done chunk rest) =
    if toRead chunk >= 1
            then
              do val <- ioe_lift $ getByte (buf chunk) (loc chunk)
                 pure (val, MkBin done (incLoc 1 chunk) rest)
              else
                case rest of
                     [] => throw "EndOfBuffer: Byte"
                     (next :: rest) =>
                        do val <- ioe_lift $ getByte (buf next) 0
                           pure (val, MkBin (chunk :: done) (incLoc 1 next) rest)

export  
Codec Int where
  toBuf (MkBin done chunk rest) val = 
       if avail chunk >= 4
         then do ioe_lift $ setInt (buf chunk) (loc chunk) val
                 pure $ MkBin done (appended 4 chunk) rest
         else do Just newbuf <- ioe_lift $ newBuffer 65536
                  | Nothing => throw "Buffer expansion failed"
                 ioe_lift $ setInt newbuf 0 val
                 pure $ MkBin (chunk :: done)
                              (MkChunk newbuf 4 (size newbuf) 4)
                              rest
  fromBuf (MkBin done chunk rest) = 
       if toRead chunk >= 4
          then do val <- ioe_lift $ getInt (buf chunk) (loc chunk)
                  pure (val, MkBin done (incLoc 4 chunk) rest)
          else case rest of
            [] => throw "EndOfBuffer: Int"
            (next :: rest) =>
              do val <- ioe_lift $ getInt (buf next) 0
                 pure (val, MkBin (chunk :: done) (incLoc 4 next) rest)

export                 
Codec a => Codec (List a) where
  toBuf bf xs = do bu <- toBuf bf (cast {to=Int} (length xs)) 
                   foldlM (\b, x => toBuf b x) bu xs
  fromBuf bf = do (len, rest) <- fromBuf bf {a=Int}
                  readElems [] (cast len) rest
    where
      readElems : List a -> Nat -> Binary -> IOE (List a, Binary) 
      readElems xs  Z    bi = pure (reverse xs, bi)
      readElems xs (S k) bi = do (val, rest) <- fromBuf {a} bi
                                 readElems (val :: xs) k rest

covering                                 
toLimbs : Integer -> List Int
toLimbs x
    = if x == 0 
         then []
         else if x == -1 then [-1]
              else fromInteger (prim__andBigInt x 0xff) ::
                    toLimbs (prim__ashrBigInt x 8)

fromLimbs : List Int -> Integer
fromLimbs [] = 0
fromLimbs (x :: xs) = cast x + prim__shlBigInt (fromLimbs xs) 8

export
Codec Integer where
  toBuf b val
    = assert_total $ if val < 0
         then do b1 <- toBuf b (the Bits8 0)
                 toBuf b1 (toLimbs (-val))
         else do b1 <- toBuf b (the Bits8 1)
                 toBuf b1 (toLimbs val)
  fromBuf b 
    = do (val, rest) <- fromBuf b {a = Bits8}
         case val of
              0 => do (val, rest2) <- fromBuf {a = List Int} rest
                      pure (-(fromLimbs val), rest2)
              1 => do (val, rest2) <- fromBuf {a = List Int} rest
                      pure (fromLimbs val, rest2)
              _ => throw "Corrupt integer"                                 