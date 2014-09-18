import Data.Word
import Data.Array
import Prelude hiding (foldl, readFile)
import Data.Bits
import Data.ByteString (readFile, unpack)

import Debug.Trace
import Numeric


import FRP.Elerea.Simple hiding (delay)
import FRP.Helm
import FRP.Helm.Time
import qualified FRP.Helm.Window as Window
import FRP.Helm.Keyboard
import FRP.Helm.Utilities

toKeyboard:: Word8 -> Key
toKeyboard 1 = Number1Key
toKeyboard 2 = Number2Key
toKeyboard 3 = Number3Key
toKeyboard 12 = Number4Key
toKeyboard 4 = QKey
toKeyboard 5 = WKey
toKeyboard 6 = EKey
toKeyboard 13 = RKey
toKeyboard 7 = AKey
toKeyboard 8 = SKey
toKeyboard 9 = DKey
toKeyboard 14 = FKey
toKeyboard 10 = ZKey
toKeyboard 0 = XKey
toKeyboard 11 = CKey
toKeyboard 15 = VKey            


data Chip8 = Chip8 { memory::Array Word16 Word8,
                     graphics::Array Int Bool,
                     register::Array Word8 Word8,
                     indexRegister::Word16,
                     programCounter::Word16,
                     stack::[Word16],
                     delayTimer::Word8
                   } deriving Show

newArray (a, b) v = array (a, b) $ [(i, v) | i<-enumFromTo a b]                    

chip8Fontset = [0xF0, 0x90, 0x90, 0x90, 0xF0, -- 0
                0x20, 0x60, 0x20, 0x20, 0x70, -- 1
                0xF0, 0x10, 0xF0, 0x80, 0xF0, -- 2
                0xF0, 0x10, 0xF0, 0x10, 0xF0, -- 3
                0x90, 0x90, 0xF0, 0x10, 0x10, -- 4
                0xF0, 0x80, 0xF0, 0x10, 0xF0, -- 5
                0xF0, 0x80, 0xF0, 0x90, 0xF0, -- 6
                0xF0, 0x10, 0x20, 0x40, 0x40, -- 7
                0xF0, 0x90, 0xF0, 0x90, 0xF0, -- 8
                0xF0, 0x90, 0xF0, 0x10, 0xF0, -- 9
                0xF0, 0x90, 0xF0, 0x90, 0x90, -- A
                0xE0, 0x90, 0xE0, 0x90, 0xE0, -- B
                0xF0, 0x80, 0x80, 0x80, 0xF0, -- C
                0xE0, 0x90, 0x90, 0x90, 0xE0, -- D
                0xF0, 0x80, 0xF0, 0x80, 0xF0, -- E
                0xF0, 0x80, 0xF0, 0x80, 0x80  -- F
               ]

defaultState = Chip8 { memory = newArray (0, 4095) 0 // zip [0..] chip8Fontset,
                       graphics = newArray (0, 2047) False,
                       register = newArray (0, 15) 0,
                       indexRegister = 0,
                       programCounter = 0x200,
                       stack = [],
                       delayTimer = 0
                     }


fromOctets :: Word8 -> Word8 -> Word16
fromOctets w1 w2 = (fromIntegral w1 `shiftL` 8) .|. fromIntegral w2

toWord4 :: Word8 -> [Word8]
toWord4 w = (w `shiftR` 4) : (w .&. 0x0F) :[]

fromWord4 :: Word8 -> Word8 -> Word8
fromWord4 w1 w2 = (fromIntegral w1 `shiftL` 4) .|. fromIntegral w2

toNNN :: [Word8] -> Word16
toNNN (n1:n2:n3:[]) =  fromOctets n1 $ fromWord4 n2 n3

toNN :: [Word8] -> Word8
toNN (n1:n2:[]) = fromWord4 n1 n2



c_00EE c = c {
  programCounter = (head $ stack c) + 2, 
  stack = tail $ stack c
}

c_00E0 c = c {
  graphics = newArray (0, 2047) False,
  programCounter = programCounter c + 2
}

c_1NNN adr c = c { programCounter = adr}

c_2NNN adr c = c {
  stack  =  (programCounter c : stack c),
  programCounter = adr
}

c_3XNN x n c = let vx = register c ! x
               in c { programCounter = programCounter c + if vx == n then 4 else 2 }

c_4XNN x n c = let vx = register c ! x
               in c { programCounter = programCounter c + if vx /= n then 4 else 2 }

c_5XY0 x y c = let vx = register c ! x
                   vy = register c ! y
               in c { programCounter = programCounter c + if vx == vy then 4 else 2 }               
               
c_6XNN x n c = c {
    register = register c // [(x,n)],
    programCounter = programCounter c + 2
  }

c_7XNN x n c = let vx = register c ! x
               in c { register = register c // [(x, vx+n)],
                      programCounter = programCounter c + 2 }
                      
c_8XY0 x y c = let vy = register c ! y
               in c { register = register c // [(x, vy)],
                      programCounter = programCounter c + 2 }  

c_8XY1 x y c = let vx = register c ! x
                   vy = register c ! y
               in c { register = register c // [(x, vx .|. vy)],
                      programCounter = programCounter c + 2 }                        

c_8XY2 x y c = let vx = register c ! x
                   vy = register c ! y
               in c { register = register c // [(x, vx .&. vy)],
                      programCounter = programCounter c + 2 } 
                      
c_8XY3 x y c = let vx = register c ! x
                   vy = register c ! y
               in c { register = register c // [(x, vx `xor` vy)],
                      programCounter = programCounter c + 2 }                                              
                      
c_8XY4 x y c = let vx = register c ! x
                   vy = register c ! y
               in c { register = register c // [(x, vx+vy), (15, if vy <= 0xff-vx then 0 else 1)],
                      programCounter = programCounter c + 2 }  
                      
c_8XY5 x y c = let vx = register c ! x
                   vy = register c ! y
               in c { register = register c // [(x, vx-vy), (15, if vx < vy then 0 else 1)],
                      programCounter = programCounter c + 2 }  

c_8XY6 x y c = let vy = register c ! y
               in c { register = register c // [(x, vy `shiftR` 1), (15, vy `shiftL` 7)],
                      programCounter = programCounter c + 2 }  

c_8XY7 x y c = let vx = register c ! x
                   vy = register c ! y
               in c { register = register c // [(x, vy-vx), (15, if vy < vx then 0 else 1)],
                      programCounter = programCounter c + 2 } 

c_8XYE x y c = let vy = register c ! y
               in c { register = register c // [(x, vy `shiftL` 1), (15, vy `shiftR` 7)],
                      programCounter = programCounter c + 2 }                        

c_9XY0 x y c = let vx = register c ! x
                   vy = register c ! y
               in c { programCounter = programCounter c + if vx /= vy then 4 else 2 }                      

c_ANNN n c = c { indexRegister = n, programCounter = programCounter c + 2 }

c_BNNN n c = c { programCounter = n + (fromIntegral $ register c ! 0) }

c_CXNN ran x n c = c { register = register c // [(x, ran .&. n)], programCounter = programCounter c + 2 }
             
c_DXYN rx ry n c = c { 
    graphics = gfx // spriteMap (\x y ->  (pixel x y, gfx!(pixel x y) /= bit x y)),
    register = register c // [(15, if or (spriteMap (\x y -> (gfx!pixel x y) && (bit x y))) then 1 else 0)],
    programCounter = programCounter c + 2
  }
  where
    gfx = graphics c
    vx = register c ! rx
    vy = register c ! ry
    i = indexRegister c
    pixel x y = (fromIntegral (vy) + fromIntegral (y))*64 + fromIntegral (vx) + fromIntegral (x)
    bit x y = (memory c ! i+y) .&. (0x80 `shiftR` x) /= 0 
    spriteMap f = [ f x y | y <- [0..(n-1)], x <- [0..7]]
    
c_EX9E inp x c = let vx = register c ! x
                 in c { programCounter = programCounter c + if toKeyboard vx `elem` inp then 4 else 2 }    

c_EXA1 inp x c = let vx = register c ! x
                 in c { programCounter = programCounter c + if not $ toKeyboard vx `elem` inp then 4 else 2 }                     
                 
c_FX07 x c = c { register = register c // [(x, delayTimer c)], programCounter = programCounter c + 2 }                     

c_FX15 x c = let vx = register c ! x
             in c { delayTimer = vx, programCounter = programCounter c + 2 }

c_FX1E x c = let vx = register c ! x
                 i = indexRegister c
             in c { indexRegister = i + fromIntegral vx, programCounter = programCounter c + 2 }

c_FX29 x c = let vx = register c ! x
             in c { indexRegister = (fromIntegral x) *5, programCounter = programCounter c + 2 }

c_FX33 x c = let vx = register c ! x
                 i = indexRegister c
                 d3 = vx `rem` 10
                 d2 = d3 `rem` 10
                 d1 = d2 `rem` 10
             in c { memory = memory c //[(i, d1),(i+1, d2), (i+2, d3)] , programCounter = programCounter c + 2 }

c_FX55 x c = let v = (!) (register c)
                 i = indexRegister c
             in c { indexRegister = i+(fromIntegral (v x))+1,
                    memory = memory c // [(i + (fromIntegral n), fromIntegral (v n)) | n <- [0..x]],
                    programCounter = programCounter c + 2 }             

c_FX65 x c = let i = indexRegister c
                 mem n = (!) (memory c) $ (+) i $ fromIntegral n
             in c { indexRegister = i+(fromIntegral (register c ! x))+1,
                    register = register c // [(n, mem n) | n <- [0..x]],
                    programCounter = programCounter c + 2 }                    
                    
niy::String -> Chip8 -> Chip8
niy str c = trace str c {programCounter = (programCounter c) + 2}

updateTimers::Chip8 -> Chip8
updateTimers chip8 = chip8 {
    delayTimer = if d > 0 then d - 1 else 0
  }
  where 
    d = delayTimer chip8


showGraphics::Chip8 -> String
showGraphics chip8 = concat $ map line $ fst $ part ([[]], elems g) 
  where g = graphics chip8
        part (acc, []) = (acc, [])
        part (acc,rest) = part (acc ++ [(take 64 rest)], drop 64 rest)
        line::[Bool] -> String
        line ls = (++) "\n" $ concat $ map (\x -> if x then "*" else " ") ls
        
    
process::(Time, [Key], Word8) -> Chip8 -> Chip8
process (t, inp, ran) chip8 =
  trace (showGraphics chip8 ++ "\n\n") $  
  --trace ("PC: "++(showHex pc "") ++" OPCODE: "++ concat (map (\x -> showHex x "") opcode) ++ " STACK: "++ (show $ stack chip8))
  (case opcode of
        0x0:0x0:0xe:0xe:[] -> c_00EE
        0x0:0x0:0xe:0x0:[] -> c_00E0
        0x0:_          :[] -> niy "####"
        0x1:           nnn -> c_1NNN $ toNNN nnn 
        0x2:           nnn -> c_2NNN $ toNNN nnn
        0x3:          x:nn -> c_3XNN x $ toNN nn
        0x4:          x:nn -> c_4XNN x $ toNN nn
        0x5:x  :y  :0x0:[] -> c_5XY0 x y
        0x6:x      :    nn -> c_6XNN x $ toNN nn
        0x7:x      :    nn -> c_7XNN x $ toNN nn
        0x8:x  :y  :0x0:[] -> c_8XY0 x y
        0x8:x  :y  :0x1:[] -> c_8XY1 x y
        0x8:x  :y  :0x2:[] -> c_8XY2 x y
        0x8:x  :y  :0x3:[] -> c_8XY3 x y
        0x8:x  :y  :0x4:[] -> c_8XY4 x y
        0x8:x  :y  :0x5:[] -> c_8XY5 x y
        0x8:x  :y  :0x6:[] -> c_8XY6 x y
        0x8:x  :y  :0x7:[] -> c_8XY7 x y
        0x8:x  :y  :0xe:[] -> c_8XYE x y
        0x9:x  :y  :0x0:[] -> c_9XY0 x y
        0xa:           nnn -> c_ANNN $ toNNN nnn
        0xb:           nnn -> c_BNNN $ toNNN nnn
        0xc:x      :    nn -> c_CXNN ran x $ toNN nn
        0xd:x  :y  :n  :[] -> c_DXYN x y n
        0xe:x  :0x9:0xe:[] -> c_EX9E inp x
        0xe:x  :0xa:0x1:[] -> c_EXA1 inp x
        0xf:x  :0x0:0x7:[] -> c_FX07 x
        0xf:x  :0x1:0x5:[] -> c_FX15 x
        0xf:x  :0x1:0x8:[] -> niy "FX18"
        0xf:x  :0x1:0xe:[] -> c_FX1E x
        0xf:x  :0x2:0x9:[] -> c_FX29 x
        0xf:x  :0x3:0x3:[] -> c_FX33 x
        0xf:x  :0x5:0x5:[] -> c_FX55 x
        0xf:x  :0x6:0x5:[] -> c_FX65 x
        _                  -> niy "!!!!") $ updateTimers chip8
  where 
    pc = programCounter chip8
    mem = memory chip8
    opcode = (toWord4 (mem!pc)) ++ ( toWord4 (mem!(pc+1)))

input :: SignalGen (Signal (Time, [Key], Word8))
input = lift3 (, ,) delta keysDown random

render :: Chip8 -> (Int, Int) -> Element
render chip8 (w, h) =
    collage w h screen
  where
    half = (/ 2). fromIntegral
    size = ((fromIntegral w /64)-2, (fromIntegral h /32)-2)
    pox p= (fromIntegral (p `rem` 64)*(fst size +2) + (fst size)/2 +1, fromIntegral (p `div` 64)*(snd size +2) + (snd size)/2 +1)
    pixel p = move (pox p) $ filled white $ rect (fst size) (snd size)
    screen = map (pixel.fst) $ filter snd (assocs $ graphics chip8)
    
loadFile path = do 
  file <- readFile path
  return $ defaultState {memory = (memory defaultState) // (zip [0x200..] $ unpack file)}
  where
    mix (i, _) val = (i+1, val)

main :: IO ()
main = do
    program <- loadFile "PONG2"
    engine <- startup config

    run engine $ render <~ (stepper program) ~~ Window.dimensions engine

  where
    config = defaultConfig { windowTitle = "Chip8Emulator", windowDimensions = (10*64, 10*32) }
    stepper p = foldp process p input