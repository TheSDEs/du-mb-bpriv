require import Int Bool Real SmtMap FSet. 
require import Distr Core List. 
require import LeftOrRight. 
require (*  *) VotingSecurity_omb. 
require (*  *) VFR Finite.

clone  include VotingSecurity_omb.

(** Types and operators **)
type label = ident.
type cipher.

op extractPk : skey  -> pkey. (* extract public key from secret key *)  
op miniPublish : (ident  * cipher) list -> pubBB. (* publish algorithm for minivoting *)

(** Distributions **)
op d_ids   : ident distr. 

(** Axioms for distributions **)
axiom d_ids_ll       : is_lossless d_ids. 
axiom is_finite_h_in : Finite.is_finite predT <:h_in>. 
axiom distr_h_out    : is_lossless dh_out. 

(* Clone the voting security theory, including the security definition *)
clone export VotingSecurity_omb as VSmv with
  type ident    <- ident,
  type vote     <- vote,
  type result   <- result,
  type pubBB    <- pubBB,
  type pubcred  <- ident,
  type secretcred <- ident,
  type ballot   <- cipher,
  type state    <- cipher,
  type pkey     <- pkey, 
  type skey     <- skey,
  type prf      <- prf,
  type h_in     <- h_in,
  type h_out    <- h_out,
  type g_in     <- g_in,
  type g_out    <- g_out,
  op dh_out     <- dh_out,
  op dg_out     <- dg_out,
  op Publish    <- miniPublish.
  
(* Clone theory for voting friendly relations *)
clone export VFR as VFRmv with
  type ident   <- ident,
  type label   <- label,
  type vote    <- vote, 
  type result  <- result,
  type cipher  <- cipher,
  type pkey    <- pkey,
  type skey    <- skey, 
  type prf     <- prf,
  type pubBB   <- pubBB,
  type h_in    <- h_in,
  type h_out   <- h_out,
  type g_in    <- g_in,
  type g_out   <- g_out, 
  op dh_out    <- dh_out,
  op dg_out    <- dg_out,
  op Rho       <- Rho,
  op Publish   <- miniPublish.  

    
(**** MiniVoting definition ****)
module MV(E:Scheme, P:Prover, Ve:Verifier, C:ValidInd, H:HOracle.POracle, G:GOracle.POracle) = {

  (* Setup algorithm generating an encryption/decryption key pair *)
  proc setup() : pkey * skey = {
    var pk, sk;
    (pk, sk) <@ E(H).kgen();
    return (pk, sk);
  }

  (* Register algorithm *)
  proc register(id:ident, pk:pkey, sk:skey) : ident * ident = {
    return (id, id);
  }

  (* Vote algorithm *)
  (* s is the state, which in this case is a ciphertext, used by voters for individual verification *)
  proc vote(pk:pkey, id:ident, pc:ident, sc:ident, v:vote) = {
    var b, s;
    b <@ E(H).enc(pk, id, v);
    s <- b;
    return (id, b, s);
  }

  (* Validboard algorithm *)
  proc validboard(bb:(ident  * cipher) list, pk:pkey) = {
    var e1, e2;
    (* idl = (id, label), b = ballot/ciphertext *)
    (* so idl.`1 = id and idl.`2 = label *)
    var idl, c;
    var i;

    e1 <- false;
    e2 <- true;

    i <- 0;
    while ( i < size bb ) {

      (idl, c) <- nth witness bb i;

      (* Check if the voter has already cast a vote *)
      if (!e1) {
        e1 <- (exists (id' : ident), !(id' = idl) /\ (id', c) \in bb);
      }

      (* Check if the ballot is correctly formed *)
      if (e2) {
        e2 <@ C(H).validInd((idl,idl, c), pk);
      }
    i <- i + 1;
    }

  return (!e1  /\ e2);
  } 

  (* Tally algorithm, decrypting all the ciphertexts on the bulletin board *)
  proc tally(bb:(ident * cipher) list, pk:pkey, sk : skey) = {
    var dbb, i, c, idl, v, r, pi;
    
    dbb <- [];
    
    i <- 0;
    while (i < size bb) {
      (idl, c) <- nth witness bb i;
         v     <@ E(H).dec(sk, idl, c);
        dbb    <- dbb ++ [(idl, v)];
         i     <- i + 1;
    }
    
    r   <$ Rho dbb;
    pk  <- extractPk sk;
    pi <@ P(G).prove((pk, miniPublish bb, r), (sk, bb)); 
    return (r, pi);
  } 

  (* Return public part of ballot box *)
  proc publish(bb: (ident * cipher) list) : pubBB = {
    return miniPublish (bb); 
  }

  (* Voters verify by checking that their identity and ciphertext is *)
  (* present on the bulletin board                                   *)
  proc verifyvote(id:ident, s:cipher, 
                  bb:(ident * cipher) list, 
                  id':ident, id'':ident) : bool = {
      return (id,s) \in bb;
  } 

  (* Verify tally by verifying the tally proof *)
  proc verifytally(st:(pkey * pubBB * result), pi:prf) = {
    var d;
    
    d <@ Ve(G).verify(st, pi);
    return d;
  }

}. 
