;; The first three lines of this file were inserted by DrRacket. They record metadata
;; about the language level of this file in a form that our tools can easily process.
#reader(lib "htdp-intermediate-lambda-reader.ss" "lang")((modname RSA-non-optimized) (read-case-sensitive #t) (teachpacks ()) (htdp-settings #(#t constructor repeating-decimal #f #t none #f () #f)))
(require math/base)

 (require math/number-theory)

;;=============================================
;;RSA Encryption Program in Racket

;;This program uses the RSA Scheme in order to
;;encrypt and decrypt ciphertext messages.

;;Limitations: Ciphertext must be some natural number (or text converted to a numerical value).
;;             Large distict primes p and q with > 300 decimal
;;             digits each must be randomly selected for sufficient
;;             security

;;RSA definition referenced from Language and Proofs in Algebra: An Introduction v.1.0
;;Copyright Faculty of Mathematics, University of Waterloo Aug 9 2018

;;=============================================

;;Program by Kai Huang, written Jan 8 2024

;;=============================================

;;DEFINITIONS:

;;a RSAPrime is an Int that is a prime number

(define-struct public-key (e n))
;;a Public-Key is (make-public-key Nat Nat)
;;Requires:
;;   gcd(e, (p-1)(q-1))= 1 and 1 < e < (p-1)(q-1) for RSAPrimes p, q
;;   n = p, q for RSAprimes p, q

(define-struct private-key (d n))
;;a Private-Key is (make-private-key Nat Nat)
;;Requires:
;;   ed ≡ 1 (mod (p-1)(q-1)) and 1 < d < (p-1)(q-1) for RSAPrimes p, q
;;   n = p, q for RSAprimes p, q

;;================   n-generation   ==============

;;(n-gen prime1 prime2) produces the product of prime1 and prime2

;;Examples:

(check-expect (n-gen 31 3) 93)
(check-expect (n-gen 2 23) 46)

;;n-gen: RSAPrime RSAPrime -> Nat

(define (n-gen prime1 prime2)
  (* prime1 prime2))

;;Tests:

(check-expect (n-gen 2293 2441) 5597213)
(check-expect (n-gen 1381 1553) 2144693)

;;==============  e-generation =======================
;;HELPER FUNCTIONS

;;(candidate-list prime1 prime2) generates a list of viable e values

;;Examples:

(check-expect (candidate-list 2 3) (list))
(check-expect (candidate-list 3 7) (list 5 7 11))

;;candidate-list: RSAPrime RSAPrime -> (listof Nat)

(define (candidate-list prime1 prime2)
  (filter (lambda (x) (= 1 (gcd x (* (- prime1 1)(- prime2 1)))))
          (build-list (- (* (- prime1 1)(- prime2 1)) 2) (lambda (x)(+ x 2)))))

;;Tests:

(check-expect (candidate-list 11 3) (list 3 7 9 11 13 17 19))
(check-expect (candidate-list 7 11) (list 7 11 13 17 19 23 29 31 37 41 43 47 49 53 59))

;;-------------------------------------------------------------


;;(select candidates acc) selects an item in a list

;;Examples:

(check-expect (select (list 1 2 3 4 5) 0) 1)
(check-expect (select (list 1 2 3 4 5) 4) 5)

;;select: (listof Nat) Nat -> Nat
;;Requires: 0 <= acc <= (length candidates)

(define (select candidates acc)
  (cond[(empty? candidates) "primes not sufficiently large"]
    [(zero? acc) (first candidates)]
       [else (select (rest candidates) (- acc 1))]))

;;Tests:

(check-expect (select (list 4 17 39 234 12 3 412 4 3) 3) 234)
(check-expect (select (list 45 23 3 43 2 64) 1) 23)

;;------------------------------------------------------------

;;(e-gen prime1 prime2 acc output) generates a list of integers e that satisfy
;;gcd(e, (prime1-1)(prime2-1))= 1 and
;;1 < e < (prime1-1)(prime2-1) for RSAPrimes prime1 prime2
;;and randomly selects an arbitrary e for the public key


;;e-gen: RSAPrime RSAPrime -> Nat
;;Requires: prime1 and prime2 are distinct

(define (e-gen prime1 prime2) 
    (select (candidate-list prime1 prime2)
                   (random-natural (length (candidate-list prime1 prime2)))))


;;====================== d-generation =======================

;;(d-gen e prime1 prime2) solves d for
;; ed ≡ 1 (mod (p-1)(q-1)) using the
;;Extended Euclidean Algorithm

;;Examples:

(check-expect (d-gen 3 5 11) 27)

;;d-gen: Nat RSAPrime RSAPrime -> Nat

(define (d-gen e prime1 prime2)
  (local[;;(row-application x1 x2 d1 d2 r1 r2) carries out EEA
         ;;row-application: Int Int Int Int Nat Nat -> Int
         (define (row-application x1 x2 d1 d2 r1 r2)
           (cond[(zero? r2) d1]
                [else (row-application x2 (- x1 (* x2 (quotient r1 r2)))
                                       d2 (- d1 (* d2 (quotient r1 r2)))
                                       r2 (- r1 (* r2 (quotient r1 r2))))]))
         ;;(d-gen d-value prime1 prime2) computes d such that
         ;;1 < d < (p-1)(q-1) for RSAPrimes p, q
         ;;d-gen: Int RSAPrime RSAPrime -> Nat

         (define (d-gen d-value prime1 prime2)
           (cond[(< d-value 0) (+ d-value (* (- prime1 1)(- prime2 1)))]
                [(> d-value 0) d-value]))]
    
  (d-gen (row-application 1 0 0 1 (* (- prime1 1)(- prime2 1)) e) prime1 prime2)))
                                       

;;========================= key generation =============================

;;(key-gen prime1 prime2) takes two primes and generates a public and private key

;;key-gen: RSAPrime RSAPrime -> (list Public-Key Private-Key)

(define (key-gen prime1 prime2)
  (local[(define output-public-key
           (make-public-key (e-gen prime1 prime2) (n-gen prime1 prime2)))]
    (list output-public-key (make-private-key (d-gen (public-key-e output-public-key) prime1 prime2)
                                              (n-gen prime1 prime2)))))
        

;;========================= Encryption ==================================

;;(encrypt message public) consumes a message and a
;;public key and encrypts it as ciphertext

;;encrypt: Nat Public-Key

(define (encrypt message public)
  (modular-expt message (public-key-e public) (public-key-n public)))

;;========================= Decryption ==================================

;;(decrypt cipher private) consumes a cipher and a public key and decrypts it

;;decrypt: Nat Private-Key

(define (decrypt cipher private)
  (modular-expt cipher (private-key-d private) (private-key-n private)))

;;=============================================================================

;;SAMPLE:

(key-gen 853 857)

(list (make-public-key 299899 497009) (make-private-key 82099 497009))

(decrypt (encrypt 39  (make-public-key 299899 497009)) (make-private-key 82099 497009))
