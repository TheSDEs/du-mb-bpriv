(* -------------------------------------------------------------------- *)
require import AllCore StdRing StdOrder Int Real Distr DBool FSet.
require (*--*) DiffieHellman PKE_CPA.
require (*--*) CyclicGroup.

(* ---------------- Sane Default Behaviours --------------------------- *)
pragma +implicits.

(* ---------------------- Let's Get Started --------------------------- *)

type space.

clone export CyclicGroup as G with
  type group <- space.

import FDistr G.

(** Construction: a PKE **)
type pkey = space.
type skey = F.t.
type ptxt = space.
type ctxt = space * space.

clone import PKE_CPA as PKE  with
  type pkey <- pkey,
  type skey <- skey,
  type ptxt <- ptxt,
  type ctxt <- ctxt.

(** Concrete Construction: ElGamal with a few algorithms in addition   **)
(** to the usual key generation, encryption and decryption algorithms: **)
(**   - Encryption algorithm where the user can specify the randomness **)
(**     used for encryption                                            **)
(**   - Trivial encryption algorithm: encrypt with randomness = zero   **)
(**   - Re-randomization of a ciphertext                               **)
(**   - An algorithm for multiplying two ciphertexts                   **)
module ElGamal  = {

  (* Key generation *)
  proc kg(): pkey * skey = {
    var sk;
    sk <$ dt;
    return (g ^ sk, sk);
  }

  (* Encryption with a user supplied randomness *)
  proc enc_c(pk:pkey, m:ptxt, y:F.t): ctxt = {
    return (g ^ y, pk ^ y * m);
  }

  (* Standard encryption *)
  proc enc(pk:pkey, m:ptxt): ctxt = {
      var y;
      y <$ dt;
      return (g^y, pk^y * m);
  }

  (* Trivial encryption *)
  proc enc_t(pk:pkey, m:ptxt) : ctxt = {
    return (g^ F.zero, pk ^ F.zero * m); 
  }

  (* Re-randomization of a ciphertext *)
  proc rerand(pk:pkey, c:ctxt, y:F.t) : ctxt = {
    var gy, gm;
    (gy, gm) <- c;
    return (gy * g^y, gm * pk^y);
  }

  (* Multiply two ciphertexts *)
  proc mult(c1:ctxt, c2:ctxt) = {
    var gy, gm, gx, gn;
    (gy, gm) <- c1;
    (gx, gn) <- c2;
    return (gy * gx, gm * gn);
  }
  
  (* Decryption *)
  proc dec(sk:skey, c:ctxt): ptxt option = {
    var gy, gm;
    (gy, gm) <- c;
    return Some (gm * gy^(-sk));
  }
}.
