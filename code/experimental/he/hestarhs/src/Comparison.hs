-- | Comparison protocols

module Comparison
    ( lambda
    , dgkClient
    , dgkServer
    , secureCompareClient
    , secureCompareServer
    ) where

import Universum

import Control.Concurrent.Async (concurrently)
import Data.Bits (testBit)
import Data.List ((!!))
import qualified Data.List.NonEmpty as NE
import System.Random (randomRIO)
import System.ZMQ4

import Hacl
import Utils


lambda :: Integral a => a
lambda = 80

----------------------------------------------------------------------------
-- DGK
----------------------------------------------------------------------------


-- | Compute r <= c jointly. Client has r, server has c.
dgkClient ::
       (Pahe sDGK, Pahe sGM)
    => Socket Req
    -> PahePk sDGK
    -> PahePk sGM
    -> Int
    -> [Integer]
    -> IO (PaheCiph sGM)
dgkClient sock pkDGK pkGM l rs =
  measureTimeSingle "dgk client" $ do
    log "Client: dgk started"
    send sock [] "init"

    let rsLen = length rs
    when (rsLen > paheK pkDGK) $ error "dgk rsLen is too big"

    log "Client: encoding rbits"
    let !rbits = map (\i -> map (\c -> bool 0 1 $ testBit c i) rs) [0..l-1]
    --log $ "Client rbits: " <> show rbits
    encRBits <- mapM (paheEnc pkDGK) rbits


    let !bitmaskNeg = map (\x -> 1 - x) <$> rbits
    log "Client: receiving"
    cs <- mapM (paheFromBS pkDGK) =<< receiveMulti sock

    log "Client: computing xors"
    xors <- forM (cs `zip` [0..]) $ \(ci,i) -> do

        -- ci * maskNeg + (1-ci) * mask
        a <- paheSIMDMulScal pkDGK ci (bitmaskNeg !! i)
        oneMinCi <- paheSIMDSub pkDGK (paheOne pkDGK) ci
        c <- paheSIMDMulScal pkDGK oneMinCi (rbits !! i)
        paheSIMDAdd pkDGK a c
    log "Client: computed xors"

    --log "XORS: "
    --print =<< mapM (paheDec skDGK) xors

    delta <- replicateM rsLen (randomRIO (0,1))
    deltaEnc <- paheEnc pkDGK delta
    let s0 = map (\i -> 1 - 2 * i) delta
    log $ "Client: s = " <> show s0
    s <- paheEnc pkDGK s0

    log "Client: computing xor sums"
    let computeXorSums i prev = do
            nextXorSum <- paheSIMDAdd pkDGK prev (xors !! i)
            xorsTail <- if i == 0 then pure [] else computeXorSums (i-1) nextXorSum
            pure $ nextXorSum : xorsTail
    xorsums <- reverse <$> computeXorSums (l-1) (paheZero pkDGK)

    --log "XOR SUBS: "
    --print =<< mapM (paheDec skDGK) xorsums

    log "Client: computing cis"
    ci <- forM [0..l-1] $ \i -> do
        a <- paheSIMDAdd pkDGK s (encRBits !! i)
        b <- paheSIMDSub pkDGK a (cs !! i)

        if i == l-1 then pure b else do
            xorsum3 <- paheSIMDMulScal pkDGK (xorsums !! (i+1)) $ replicate rsLen 3
            paheSIMDAdd pkDGK b xorsum3

    xorsumFull3 <- paheSIMDMulScal pkDGK (xorsums !! 0) $ replicate rsLen 3
    cLast <- paheSIMDAdd pkDGK deltaEnc xorsumFull3

    --log "CIs: "
    --print =<< mapM (paheDec skDGK) (cLast : ci)
    log "CIs were computed"

    ciShuffled <- shuffle =<< mapM (paheMultBlind pkDGK) (cLast : ci)

    --log "CIs shuffled/blinded: "
    --print =<< mapM (paheDec skDGK) ciShuffled

    sendMulti sock =<< (NE.fromList <$> mapM (paheToBS pkDGK) ciShuffled)
    log "Client: sent, waiting"
    zs <- paheFromBS pkGM =<< receive sock
    log "Client: computing eps"

    let compeps = do
          let sMask = map (bool 1 0 . (== 1)) s0
          let sMaskNeg = map (\x -> 1 - x) sMask
          -- zs * s + (1-zs) * neg s
          a <- paheSIMDMulScal pkGM zs sMask
          oneMinZs <- paheSIMDSub pkGM (paheOne pkGM) zs
          c <- paheSIMDMulScal pkGM oneMinZs sMaskNeg
          paheSIMDAdd pkGM a c

    eps <- compeps

    log "Client: dgk ended"
    pure eps

dgkServer ::
       (Pahe sDGK, Pahe sGM)
    => Socket Rep
    -> PaheSk sDGK
    -> PaheSk sGM
    -> Int
    -> [Integer]
    -> IO ()
dgkServer sock skDGK skGM l cs = do
    log "Server: dgk started"
    let pkDGK = paheToPublic skDGK
    let pkGM = paheToPublic skGM
    let csLen = length cs

    let cbits = map (\i -> map (\c -> bool 0 1 $ testBit c i) cs) [0..l-1]
    --log $ "Server cbits: " <> show cbits

    cbitsToSend <- mapM (paheToBS pkDGK <=< paheEnc pkDGK) cbits

    log $ "Server received, sending to client"
    _ <- receive sock
    sendMulti sock $ NE.fromList cbitsToSend

    log $ "Server: computing zeroes"
    es <- mapM (paheFromBS pkDGK) =<< receiveMulti sock
    esZeroes <-
        mapM (fmap (take csLen) . paheIsZero skDGK) es
    let zeroes = map (bool 0 1) $
                 foldr (\e acc -> map (uncurry (&&)) $ zip e acc)
                       (replicate csLen True)
                       (map not <$> esZeroes)

    log $ "Server zeroes: " <> show zeroes

    enczeroes <- paheEnc pkGM zeroes
    send sock [] =<< paheToBS pkGM enczeroes

    log "Server: dgk exited"


----------------------------------------------------------------------------
-- Secure Comparison
----------------------------------------------------------------------------

-- | Compute y <= x jointly with secret inputs. Client has r, server has c.
secureCompareClient ::
       (Pahe sTop, Pahe sDGK, Pahe sGM)
    => Socket Req
    -> PahePk sTop
    -> PahePk sDGK
    -> PahePk sGM
    -> Int
    -> Int -- how many to SIMD compare
    -> PaheCiph sTop
    -> PaheCiph sTop
    -> IO (PaheCiph sGM)
secureCompareClient sock pkTop pkDGK pkGM l m x y =
  measureTimeSingle "secure compare client" $ do

    log "Client: secureCompare started"
    when (m > paheK pkDGK) $ error "Secure compare: m is too big"

    rhos::[Integer] <- replicateM m $ randomRIO (0, 2^(l + lambda) - 1)
    s1 <- paheSIMDAdd pkTop x =<< paheEnc pkTop (map (+(2^l)) rhos)
    gamma <- paheSIMDSub pkTop s1 y

    send sock [] =<< paheToBS pkTop gamma

    cDiv2l <- paheFromBS pkGM =<< receive sock

    eps <- dgkClient sock pkDGK pkGM l $ map (`mod` (2^l)) rhos
    epsNeg <- paheNeg pkGM eps

    rDiv2l <- paheEnc pkGM $ map (`div` (2^l)) rhos
    rPlusEpsNeg <- paheSIMDAdd pkGM rDiv2l epsNeg
    delta <- paheSIMDSub pkGM cDiv2l rPlusEpsNeg

    log "Client: secureCompare exited"
    pure delta

secureCompareServer ::
       (Pahe sTop, Pahe sDGK, Pahe sGM)
    => Socket Rep
    -> PaheSk sTop
    -> PaheSk sDGK
    -> PaheSk sGM
    -> Int
    -> Int
    -> IO ()
secureCompareServer sock skTop skDGK skGM l m = do
    let pkTop = paheToPublic skTop
    let pkGM = paheToPublic skGM
    log "Server: securecompare started"

    gamma <- (paheDec skTop <=< paheFromBS pkTop) =<< receive sock
    let cMod2 = map (`mod` (2^l)) $ take m gamma
    let cDiv2 = map (`div` (2^l)) $ take m gamma
    send sock [] =<< (paheToBS pkGM =<< paheEnc pkGM cDiv2)


    dgkServer sock skDGK skGM l cMod2
    log "Server: securecompare exited"

----------------------------------------------------------------------------
-- Tests
----------------------------------------------------------------------------

_testCmp :: IO ()
_testCmp =
    withContext $ \ctx ->
    withSocket ctx Req $ \req ->
    withSocket ctx Rep $ \rep -> do
      putTextLn "Initialised the context, generating params"
      bind rep "inproc://argmax"
      connect req "inproc://argmax"

      putTextLn "Keygen..."
      -- SIMD parameter
      let k = 16
      -- bit size of numbers we compare
      let l = 64
      m <- randomRIO (1,k)

      -- system used to carry long secureCompare results
      skTop <- paheKeyGen @PailSep k (2^(lambda + l + 100))
      --let skTop = skDGK
      let pkTop = paheToPublic skTop

      -- system used for DGK comparison
      --skDGK <- paheKeyGen @PailSep k (2^(lambda+l))
      skDGK <- paheKeyGen @DgkCrt k (5 + 3 * fromIntegral l)
      let pkDGK = paheToPublic skDGK

      -- system used to carry QR results
      skGM <- paheKeyGen @GMSep k (2^(l+5))
      --let skGM = skDGK
      let pkGM = paheToPublic skGM

      let testCompare = replicateM_ 10 $ do
              xs <- replicateM m $ randomRIO (0,2^l-1)
              ys <- replicateM m $ randomRIO (0,2^l-1)
              let expected = map (\(x,y) -> x >= y) $ zip xs ys

              xsEnc <- paheEnc pkTop xs
              ysEnc <- paheEnc pkTop ys

              (gamma,()) <-
                  measureTimeSingle "SecureCompare" $
                  concurrently
                  (secureCompareClient req pkTop pkDGK pkGM l m xsEnc ysEnc)
                  (secureCompareServer rep skTop skDGK skGM l m)

              secCompRes <- paheDec skGM gamma
              unless (expected `isPrefixOf` map (==1) secCompRes) $ do
                  print xs
                  print ys
                  putTextLn $ "Expected: " <> show expected
                  putTextLn $ "Got:      " <> show secCompRes
                  putTextLn $ "          " <> show (map (==1) secCompRes)
                  error "Mismatch"

      let testDGK = replicateM_ 100 $ do
              cs <- replicateM (k-4) $ randomRIO (0,2^l-1)
              rs <- replicateM (k-4) $ randomRIO (0,2^l-1)
              let expected = map (\(c,r) -> r <= c) $ zip cs rs

              putTextLn "Starting the protocol"
              (eps,()) <-
                  concurrently
                  (dgkClient req pkDGK pkGM l rs)
                  (dgkServer rep skDGK skGM l cs)

              dgkRes <- map (== 1) <$> paheDec skGM eps
              unless (expected `isPrefixOf` dgkRes) $ do
                  print cs
                  print rs
                  putTextLn $ "Expected: " <> show expected
                  putTextLn $ "Got:      " <> show dgkRes
                  error "Mismatch"

      --testDGK
      testCompare