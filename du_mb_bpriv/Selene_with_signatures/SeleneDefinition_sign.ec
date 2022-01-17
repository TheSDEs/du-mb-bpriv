require import Int Bool Real SmtMap FSet Perms DList. 
require import Distr Core List CyclicGroup. 
require import LeftOrRight. 
require (*  *) VotingSecurity_mb_sign. 
require (*  *) ElGamal LPKE Finite ProofSystem.  

clone include VotingSecurity_mb_sign. 

type cipher. 
type tracker = ident.

(* Commitment keys *)
type upkey = ident. (* We treat ident as a group where DDH is hard *)
type uskey.

(* Keys for encryption and decryption *)
type epkey.
type eskey. 
op get_epk : eskey -> epkey.

(* Operator removing the third element in each triple in a list *)
op rem_trd (l: ('a * 'b * 'c) list) = map (fun (x: 'a * 'b * 'c), (x.`1,x.`2)) l.   

(** PKE for trackers **)
clone export ElGamal as PKEtr with
type  space <- ident.

(*** zero-knowledge for setup ***)
type trackerProof.
type commitmentProof.

op setupTrackers : (ctxt list * (ident, ctxt) fmap) * (tracker list * skey) -> trackerProof.
op setupCommitments : (ctxt * ctxt * ptxt option) * (t * skey) -> commitmentProof.


(****************************************************************************************************)
(******** Commitment scheme, inspired by CommitmentProtocol.ec on the EasyCrypt github repo *********)
(****************************************************************************************************)

type commitment = ident.
type opening = ident * t. 

module type CommitmentProtocol = {
  proc gen()                                    : upkey * uskey 
  proc commit(upk:upkey,tr:tracker)             : commitment * opening 
  proc open(upk:upkey, c:commitment, d:opening) : tracker 
}.


(****************************************************************************************************)
(********                           Signature Scheme                                        *********)
(****************************************************************************************************)

type supkey, suskey.
type message = cipher.
type signature. 

module type SignatureScheme = {
  proc gen()                                       : supkey * suskey 
  proc sign  (supk:suskey, m:message)              : signature 
  proc verify(supk:supkey, m:message, s:signature) : bool 
}.

(****************************************************************************************************)
(****************************************************************************************************)

(** Publish algorithm for Selene with signatures **) 
op sPublish : ((ident * upkey * supkey * commitment) * cipher * signature) list -> 
              ((ident * upkey * supkey * commitment) * cipher * signature) list.

(* axioms for random oracles *)
axiom is_finite_h_in : Finite.is_finite predT <:h_in>. 
axiom distr_h_out    : is_lossless dh_out.  


(* We need to leak information from setup. We do this by adding information to public key *)
type aux = ident fset * ctxt list * (ident, ctxt) fmap * 
           (ident, upkey) fmap * (ident, commitment) fmap * 
           trackerProof * commitmentProof list.

(* Clone the theory with the security definition *)  
clone export VotingSecurity_mb_sign as VSsmv with 
  type ident      <- ident,
  type vote       <- vote,
  type result     <- (vote list) * (ptxt list),
  type pubBB      <- ((ident * upkey * supkey * commitment) * cipher * signature) list,
  type pubcred    <- ident * upkey * supkey * commitment,
  type secretcred <- opening * suskey,
  type ballot     <- cipher,
  type saux       <- signature,
  type state_pre  <- cipher * signature,
  type state_post <- vote,
  type pkey       <- epkey * PKEtr.pkey * aux,
  type skey       <- (ident, opening) fmap * eskey * PKEtr.skey, 
  type prf        <- prf,
  type h_in       <- h_in,
  type h_out      <- h_out,
  type g_in       <- g_in,
  type g_out      <- g_out,
  op dh_out       <- dh_out,
  op dg_out       <- dg_out,
  op Publish      <- sPublish. 


(** Labelled PKE for votes **)
clone export LPKE as PKEvo with
  type label  <- ident,
  type plain  <- vote,
  type cipher <- cipher,
  type pkey   <- epkey,
  type skey   <- eskey,
  type h_in   <- h_in,
  type h_out  <- h_out,
  op   dout   <- dh_out. 

(* Clone proof system with correct types for Selene with signatures *)
clone export ProofSystem as PSvf with
  type stm   <- (epkey * PKEtr.pkey * aux) * 
                ((ident * upkey * supkey * commitment) * cipher *signature) list * 
                ((vote list) * (ptxt list)), 
  type wit   <- ((ident,opening) fmap * eskey * PKEtr.skey) * 
                ((ident * upkey * supkey * commitment) * cipher * signature) list,
  type prf   <- prf,
  type g_in  <- g_in,
  type g_out <- g_out,
  op   dout  <- dg_out
  proof *. 


(*** Selene with signatures definition ***)

(* Algorithm to check if ballots are correctly formed *)
module type ValidIndS (H:HOracle.POracle) = {
  proc valid(b:(ident * upkey * supkey * commitment) * cipher * signature, pk:epkey) : bool
}.

(* The definition of Selene with signatures *)
module Selene(Ev:PKEvo.Scheme, P:Prover, Ve:Verifier, 
              C:ValidIndS, CP:CommitmentProtocol, 
              S: SignatureScheme,
              H:HOracle.POracle, G:GOracle.POracle) = {
  
  (* Setup algorithm generating encryption and decryption keys and trackers and tracker commitments *)
  proc setup() = {

    (* list of trackers *)
    (* permuted list of identities *)
    var trL : tracker list;
    var tpTr : ctxt list;
    
    (* map from ident to cipher *)
    var pTr : (ident, ctxt) fmap;

    (* map from ident to user public key *)
    var pPk : (ident, upkey) fmap;

    (* map from ident to tracker commitment *)
    var pCo : (ident, commitment) fmap;

    (* map from ident to commitment opening *)
    var pOp : (ident, opening) fmap;
    
    (* proof that commitments are correctly formed *)
    var pi2 : commitmentProof list;
    
    var i, id, et1, et2, et3;
    var vpk, vsk;
    var tpk, tsk;
    var c, t;

    var upk, usk;
    var pi1;
    
    (* Initialize variables used for tracker generation *)
    trL   <- [];
    tpTr  <- [];
    pTr   <- empty;
    pPk   <- empty; 
    pCo   <- empty;
    pOp   <- empty;
    pi2 <- [];
    
    (* Generate encryption and decryption keys for vote *) 
    (vpk, vsk) <@ Ev(H).kgen();

    (* Generate encryption and decryption keys for tracker *)
    (tpk, tsk) <@ PKEtr.ElGamal.kg(); 
    
    (* Create the trivial encryption *)
    i <- 0;
    while (i < card BP.setidents) {
      et1  <@ PKEtr.ElGamal.enc_t(tpk, nth witness (elems BP.setidents) i);
      tpTr <- et1 :: tpTr;

      i <- i + 1;
    }
     
    (* Choose a random permutation for the voter identitites *)
    trL <$ duniform (allperms (elems BP.setidents));
    
    (* Create a fresh encryption of a random tracker to every identity,
        this is the output of the re-encryption mixnet *)
    i <- 0;
    while (i < card BP.setidents) {
      id       <- nth witness (elems BP.setidents) i;
      et1      <@ PKEtr.ElGamal.enc(tpk, nth witness trL i); 
      pTr.[id] <- et1;

      (* Generate the commitment keys *)
      (upk, usk) <@ CP.gen();
      pPk.[id]   <- upk;

      i <- i + 1;
    }

    (* The proof of shuffle for the mixed trackers *)
    pi1 <- setupTrackers((tpTr, pTr),(trL, tsk));
    
   (* Generation of Tracker number commitments *)
   i <- 0;
   while (i < card BP.setidents) {
      id <- nth witness (elems BP.setidents) i;
      
      t <$ FDistr.dt; 
      et1 <@ PKEtr.ElGamal.enc(tpk, (oget pPk.[id])^t);
      et2 <@ PKEtr.ElGamal.enc(tpk, PKEtr.G.g^t);

      et3 <@ PKEtr.ElGamal.mult(et1, oget pTr.[id]);
      c <@ PKEtr.ElGamal.dec(tsk, et3);

      (* The proof that et1 and et2 are correctly constructed and c is the correct decryption et3  *)
      pi2 <- setupCommitments((et1,et2,c),(t,tsk)) ::  pi2;

      pCo.[id] <- oget c;
      pOp.[id] <- (nth witness trL i, t);
      
      i <- i + 1;
    }

   (* Public data: encryption keys, identities, trackers, user public keys, commitments, proofs *)
   (* Secret data: commitment openings and decryption keys *)
   return ((vpk,tpk,(BP.setidents, tpTr, pTr, pPk, pCo, pi1, pi2)), 
           (pOp,vsk,tsk));  
  }

  (* Registration: each identity gets a key pair and a commitment to a tracker *)
  proc register(id:ident, pd:(epkey * PKEtr.pkey * aux), 
                sd:((ident, opening) fmap * eskey * PKEtr.skey)) = {
    
    var d, uk, c, supk, susk;
    
    (* Get the opening  belonging to id *)
    d  <- oget sd.`1.[id];
    uk <- oget pd.`3.`4.[id];
    c  <- oget pd.`3.`5.[id];

    (* Add Signatures *)
    (supk, susk) <@ S.gen();

     return ((id, uk, supk, c), (d, susk));    
  }

  (* Publish *)
  proc publish(bb: ((ident * upkey * supkey * commitment) * cipher* signature) list) = {
    return sPublish bb;
  }
  
  (* Voting procedure: return a ballot with the first element being the   *)
  (* public credential, i.e. ident, upk, commitment and the second, third *)
  (* and fourth elements being encrypted vote, state_pre and state_post   *)
  proc vote(pd:(epkey * PKEtr.pkey * aux), 
            id:ident, 
            pc:(ident * upkey * supkey * commitment), 
            sc:opening * suskey, 
            v :vote) = {
    var ev, b, s ;
    ev <@ Ev(H).enc(pd.`1, id, v);
    s  <@ S.sign(sc.`2, ev);
    b  <- (pc, ev, s, (ev,s), v);
    return b;
  }

  (* Check if board is valid *)
  proc validboard(bb:((ident * upkey * supkey * commitment) * cipher* signature) list, 
                  pd:(epkey * PKEtr.pkey * aux)) = {
    var i;
    var b, id, upk, supk, ev, ct,s;
    var e1, e2, e3;

    e1 <- false;
    e2 <- true;
    e3 <- true;

    i <- 0;
    while (i < size bb /\ (!e1 /\ e2 /\ e3)) {
        b <- nth witness bb i; (* pick ith element from bb *)
      
        id  <- b.`1.`1;
        upk <- b.`1.`2;
        supk<- b.`1.`3;
        ct  <- b.`1.`4;
        (ev,s)  <- (b.`2,b.`3);
      
        (* ids are unique? *)
          e1 <- exists (id' : ident), !(id' = id) /\ ((id', upk, supk, ct), ev, s) \in bb;

        (* ballot is well formed? *)
          e2 <@ C(H).valid(((id,upk,supk,ct),ev,s), pd.`1);

        (* public credentials correspond to id? *)
          e3 <- (oget BP.pubmap.[id] = (id,upk,supk,ct));

      i <- i + 1;

    }
    return (!e1 /\ e2 /\ e3);
  }

  (* Tally procedure *)
  proc tally(bb:((ident * upkey * supkey * commitment) * cipher * signature) list, 
             pd:(epkey * PKEtr.pkey * aux), 
             sd:((ident, opening) fmap  * eskey * PKEtr.skey)) = {
    var i, rL, vL, tL;
    var id, ev, s, vt;
    var v, tr, pi;
    var b;

    rL <- [];
    
    i <- 0;
    while (i < size bb) {
      b  <- nth witness bb i;
      (ev,s) <- (b.`2,b.`3);
      id <- b.`1.`1;
      v  <@ Ev(H).dec(sd.`2, id, ev);
      tr <@ PKEtr.ElGamal.dec(sd.`3, oget pd.`3.`3.[id]);
      rL <- (oget v, oget tr) :: rL;
      i  <- i + 1;
    }

    (* Multiset counting function: return the list of (tracker, vote) pairs in random order *)
    vt <$ (duniform (allperms rL));

    pi <@ P(G).prove((pd, sPublish bb, (unzip1 vt, unzip2 vt)), (sd, bb));

    vL <- unzip1 vt;
    tL <- unzip2 vt;
    return ((vL,tL), pi);
  }

  (* Verify the proof of correct tally *)
  proc verifytally(st:( (epkey * PKEtr.pkey * aux) * 
                        ((ident * upkey * supkey * commitment) * cipher * signature) list * 
                         (vote list * tracker list)), 
                        pi:prf) = {
    
    var d, vL, tL, rL, pd, pbb, pf;
    pd  <- st.`1;
    pbb <- st.`2;
    vL  <- st.`3.`1;
    tL  <- st.`3.`2;
    pf  <- pi;
    rL  <- zip vL tL;
    d   <@ Ve(G).verify( ((pd, pbb, (vL,tL)), pf)) ;
  
    return d;
  }

  (* Verify that your vote is part of the result *)
  (* Result is a list containing votes and trackers in random order *)
  proc verifyvote(id  : ident, 
                  spr : cipher * signature,
                  spo : vote,
                  bb  : ((ident * upkey * supkey * commitment) * cipher * signature) list, 
                  rp  : (vote list * ptxt list) * prf, 
                  pc  : (ident * upkey * supkey * commitment), 
                  sc  : opening * suskey) = {

     var tr, rL, vL, tL, v;

     v <- spo;

     (* open tracker commitment *)
     tr <@ CP.open(pc.`2, pc.`4, sc.`1);

     (* get list of votes *)
     vL <- rp.`1.`1;

     (* get list of trackers *)
     tL <- rp.`1.`2;

     (* zip lists of votes and trackers to get a list of the form (vote,tracker) list *)
     rL <- zip vL tL;

     (* check if your vote is in the zipped vote/tracker list *)
     return ( (v, tr) \in rL );
  }

}. 
 
section Typecheck. 

require import Real. 

declare module H  <: HOracle.Oracle. 
declare module G  <: GOracle.Oracle. 
declare module A  <: DU_MB_BPRIV_adv. 
declare module S  <: DU_MB_BPRIV_simulator. 
declare module R  <: Recover'. 
declare module Ev <: PKEvo.Scheme. 
declare module P  <: Prover. 
declare module Ve <: Verifier. 
declare module C  <: ValidIndS. 
declare module CP <: CommitmentProtocol. 
declare module SS <: SignatureScheme.

local lemma selene_typecheck &m :
  exists eps,
  `|Pr[DU_MB_BPRIV_L(Selene(Ev,P,Ve,C,CP,SS),A,H,G).main() @ &m : res] 
    - Pr[DU_MB_BPRIV_R(Selene(Ev,P,Ve,C,CP,SS),A,H,G,S,R).main() @ &m : res] | 
    <= eps by []. 

end section Typecheck. 
