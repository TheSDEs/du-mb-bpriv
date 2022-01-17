require import Int Bool Real SmtMap FSet. 
require import Distr Core List. 
require import LeftOrRight. 
require (*  *) VotingSecurity_mb. 
require (*  *) VFR Finite.


(**** Types and operators ****)

type ident, cipher, skey, pkey, vote, result.

type label = ident.

(* compute public key from secret key *)  
op getPK : skey  -> pkey.   

(* identity to label  *)  
op Flabel : ident  -> label = idfun.

(* bound nr of challenge queries *)
op n : { int | 0 < n } as n_pos. 


(* last vote policy : keep vote option*)
op Policy['a] (L: (ident * 'a) list): 'a list =
    with L = "[]"          => []
    with L = (::) idv L => if has ((\o) (pred1 idv.`1) fst) L
                               then Policy L
                               else idv.`2 :: Policy L.

(* remove invalid votes *) 
op valid['a] (x: ('a option) list): 'a list
   = pmap idfun x.

(* some counting method *)
op Count: vote list -> result distr. 

(* Rho operator *)
op Rho (L : (ident * vote option) list): result distr
   = Count (valid  (Policy L)).


clone export VotingSecurity_mb as VSmv with
  type ident      <- ident,
  (* label as pub credential *)
  type pubcred    <- label, 
  (* no secret credential *)
  type secretcred <- unit, 
  type result     <- result,
  type vote       <- vote,
  type ballot     <- cipher,
  type state_pre  <- cipher,
  type state_post <- cipher,
  type pkey       <- pkey, 
  type skey       <- skey,
  op Rho          <- Rho 
  proof *.

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
  op Publish   <- Publish,
  op n         <- n
  proof *.
  realize n_pos by apply n_pos. 

(** Axioms for distributions **)
axiom is_finite_h_in : Finite.is_finite predT <:h_in>. 
axiom distr_h_out    : is_lossless dh_out. 
    

(** ValidInd: well-formness of ciphertext **)
module type ValidInd (H:HOracle.POracle) = {
  proc validInd(b : (label * cipher), pk:pkey) : bool { H.o }
}.

(**** MiniVoting definition ****)
print VSmv.VotingScheme.
module (MV(E:Scheme, P:Prover, Ve:Verifier, C:ValidInd): VotingSystem) 
           (H:HOracle.POracle, G:GOracle.POracle) = {
      
  (** Setup algorithm generating an encryption/decryption key pair **)
  proc setup() : pkey * skey = {
    var pk, sk;
    (pk, sk) <@ E(H).kgen();
    return (pk, sk);
  }

  (* register: return user's label *)
  proc register(id:ident, pk:pkey, sk:skey) : label * unit = {
    return (Flabel id, tt);
  }

  (* s is the state, which in this case is a ciphertext, 
     used by voters for individual verification *)
  proc vote(pk:pkey, id:ident, pc:label, sc:unit, v:vote) = {
    var b, s;
   
    b <@ E(H).enc(pk, pc, v);
    s <- b;
    return (pc, b, s, s);
  }

  (* validboard: check if ids are unique and that ballots are well-formed *)
  proc validboard(bb:(label * cipher) list, pk:pkey) = {
    var e1, e2;
    var idl, c;
    var i;

    e1 <- false;
    e2 <- true;

    i <- 0;
    while ( i < size bb ) {

      (idl, c) <- nth witness bb i;

      if (!e1) {
        e1 <- (exists (id' : label), !(id' = idl) /\ (id', c) \in bb);
      }

      if (e2) {
        e2 <@ C(H).validInd((idl, c), pk);
      }
    i <- i + 1;
    }

  return (!e1  /\ e2);
  } 

  (* tally: decrypt ballots and return result along with proof of correct tally *)
  proc tally(bb:(label * cipher) list, pk:pkey, sk : skey) = {
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
    pk  <- getPK sk;
    pi <@ P(G).prove((pk, Publish bb, r), (sk, bb)); 
    return (r, pi);
  } 

  (* public part of ballot box *)
  proc publish(bb: (label * cipher) list) : pubBB = {
    return Publish (bb); 
  }

  (* verify vote: check if your encrypted ballot is in the ballot box *)
  proc verifyvote(id:ident, 
                  s_pre : cipher,
                  s_post: cipher,
                  bb:(label * cipher) list, 
                  bbstar:(result * prf),
                  pc:label,
                  sc:unit): bool = {
      return (pc, s_pre) \in bb;
  } 

  (* verify that the tally proof is valid using the verifier from the proof system *)
  proc verifytally(st:(pkey * pubBB * result), pi:prf) = {
    var d;
    
    d <@ Ve(G).verify(st, pi);
    return d;
  }

}. 


