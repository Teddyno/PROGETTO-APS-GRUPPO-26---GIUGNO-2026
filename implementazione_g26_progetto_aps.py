import os
import time
import sys
import random
import hashlib
from cryptography.hazmat.primitives.asymmetric import rsa, padding
from cryptography.hazmat.primitives import hashes
from cryptography.hazmat.primitives import serialization
from cryptography.exceptions import InvalidSignature


def sha256(data):
    digest=hashes.Hash(hashes.SHA256())
    digest.update(data)
    return digest.finalize()

#Simulazione di un token alfanumerico
def genera_token(length=16):
    caratteri='0123456789ABCDEFGHIJKLMNOPQRSTUVWXYZabcdefghijklmnopqrstuvwxyz'
    return ''.join(random.choice(caratteri) for _ in range(length))

# ==========================================
# ATTORI DEL SISTEMA
# ==========================================

class AutoritaRegistrazione:
    def __init__(self):
        self.db_token_hash={}
        self.lista_id_elettori=[]
        self.private_key=rsa.generate_private_key(public_exponent=65537,key_size=2048)
        self.public_key=self.private_key.public_key()

    def get_lista(self):
        return self.lista_id_elettori

    def registra_avente_diritto(self,cf):
        #Genera il token Out-of-Band
        token=genera_token()
        #Salva solo l'hash per sicurezza (Data-at-Rest)
        hash_token=sha256(token.encode())
        self.db_token_hash[cf]=hash_token
        return token

    def valida_e_rilascia_certificato(self,cf,token,pk_e):
        #L'elettore presenta CF e Token all'AR per identificarsi
        hash_token = sha256(token.encode())

        if cf in self.db_token_hash and self.db_token_hash[cf]==hash_token:
            del self.db_token_hash[cf] # Burn-after-reading: il token si autodistrugge

            #Genera lo pseudonimo ID_AR da mettere nel certificato (CERT_E) dell'elettore
            salt=os.urandom(16)
            id_ar=sha256(cf.encode()+salt)
            self.lista_id_elettori.append(id_ar)

            #pk_e viene viene convertita in bytes per essere concatenata a id_ar,
            #non si può usare encode() perché l'oggetto public_key non lo implementa a differenza di string
            pk_bytes=pk_e.public_bytes(
                encoding=serialization.Encoding.PEM,
                format=serialization.PublicFormat.SubjectPublicKeyInfo
            )
            dati_da_firmare=id_ar+pk_bytes
            firma = self.private_key.sign(
                dati_da_firmare,
                padding.PSS(mgf=padding.MGF1(hashes.SHA256()), salt_length=padding.PSS.MAX_LENGTH),
                hashes.SHA256()
            )
            certificato = {
                "id_ar":id_ar,
                "pk_e":pk_e, #Messa in chiaro affinché l'AE la legga
                "firma_ar":firma    #La prova di autenticità
            }
            print("  [AR]: Token valido. Certificazione avvenuta.")
            return certificato
        return None

class AutoritaElettorale:
    def __init__(self):
        self.pepper=b"PepperSegretoAE"
        self.lista_elettorale={} #{id_pepper: flag_voto}
        self.urna=[]             #Lista dei crittogrammi
        self.merkle_leaves=[]    #Foglie del Merkle Tree
        self.session_tokens=set()

        #Generazione prima copppia di chiavi AE (per cifrare e decifrare i voti)
        self.private_key1=rsa.generate_private_key(public_exponent=65537,key_size=2048)
        self.public_key1=self.private_key1.public_key()

        #Generazione seconda copppia di chiavi AE (per firmare le ricevute)
        self.private_key2=rsa.generate_private_key(public_exponent=65537,key_size=2048)
        self.public_key2=self.private_key2.public_key()

        #Simulazione Threshold Scheme: la chiave è "bloccata" e serve il quorum
        self.chiave_ricostruita=False

    def set_lista_elettorale(self,lista_id_ar):
        for id_ar in lista_id_ar:
            self.inserisci_in_lista(id_ar)

    def inserisci_in_lista(self,id_ar):
        #Calcola IDpepper
        if isinstance(id_ar, str):
            id_ar = id_ar.encode()
        id_pepper=sha256(id_ar+self.pepper)
        self.lista_elettorale[id_pepper]=0 #Flag, indica che non ha votato

    def autentica_con_certificato(self,cert_e,public_key_ar):
        id_ar_estratto=cert_e["id_ar"]
        pk_e_estratto=cert_e["pk_e"]
        firma_ar=cert_e["firma_ar"]

        pk_bytes=pk_e_estratto.public_bytes(
            encoding=serialization.Encoding.PEM,
            format=serialization.PublicFormat.SubjectPublicKeyInfo
        )
        dati_da_verificare=id_ar_estratto+pk_bytes

        try:
            public_key_ar.verify(
                firma_ar,
                dati_da_verificare,
                padding.PSS(mgf=padding.MGF1(hashes.SHA256()), salt_length=padding.PSS.MAX_LENGTH),
                hashes.SHA256()
            )
            print("  [AE] Firma del certificato VALIDA. Certificato autentico emanato dall'AR.")
        except InvalidSignature:
            raise Exception("  [AE] ALLARME: Firma del certificato NON VALIDA. Possibile frode!")

        nonce=os.urandom(32)
        return nonce

    def verifica_nonce(self,nonce,firma_e,cert_e):
        pk_e = cert_e["pk_e"]

        try:
            pk_e.verify(
                firma_e,
                nonce,
                padding.PSS(mgf=padding.MGF1(hashes.SHA256()), salt_length=padding.PSS.MAX_LENGTH),
                hashes.SHA256()
            )
            print("  [AE] Challenge Superata! Proof of Possession confermata.")
        except InvalidSignature:
            raise Exception("  [AE] FRODE: La firma della sfida non corrisponde al certificato!")

        id_pepper=sha256(cert_e["id_ar"]+self.pepper)

        if id_pepper in self.lista_elettorale and self.lista_elettorale[id_pepper]==0:
            self.lista_elettorale[id_pepper]=1
            session_token=genera_token()
            self.session_tokens.add(session_token)
            return session_token
        print("  Elettore non trovato!")
        return None

    def ricevi_voto(self,session_token,cv):
        if session_token not in self.session_tokens:
            raise Exception("Session Token invalido o Replay Attack!")

        #Invalida il session token (prevenzione Replay Attack)
        self.session_tokens.remove(session_token)

        #Inserisce nell'urna e crea la foglia per il Merkle Tree
        self.urna.append(cv)
        h_cv=sha256(cv)
        self.merkle_leaves.append(h_cv)
        timestamp=str(int(time.time()))
        dati_da_firmare=h_cv+timestamp.encode()
        firma=self.private_key2.sign(
            dati_da_firmare,
            padding.PSS(mgf=padding.MGF1(hashes.SHA256()), salt_length=padding.PSS.MAX_LENGTH),
            hashes.SHA256()
        )

        ricevuta={
            "cv":cv,
            "timestamp":timestamp,
            "firma":firma
        }
        return ricevuta

    def _hash_pair(self,left,right):
        return sha256(left+right)

    def genera_merkle_tree_e_proofs(self):
        if not self.urna:
            raise Exception("  [AE] L'urna è vuota. Impossibile creare il Merkle Tree.")

        print("  [AE] Calcolo degli Hash dei crittogrammi H(C_v)...")
        # Calcoliamo H(C_v) per ogni voto e li ordiniamo per garantire l'anonimato temporale
        foglie=sorted([sha256(cv) for cv in self.urna])

        # Salviamo i livelli dell'albero. tree[0] sono le foglie, tree[-1] sarà la radice.
        tree=[foglie]
        livello_corrente=foglie

        # Costruzione dell'albero (Bottom-Up)
        while len(livello_corrente)>1:
            livello_successivo=[]
            # Saltiamo di 2 in 2
            for i in range(0,len(livello_corrente),2):
                nodo_sinistro=livello_corrente[i]

                # Se il numero di nodi è dispari, duplichiamo l'ultimo (standard Merkle)
                if i+1<len(livello_corrente):
                    nodo_destro=livello_corrente[i + 1]
                else:
                    nodo_destro=nodo_sinistro

                hash_padre=self._hash_pair(nodo_sinistro, nodo_destro)
                livello_successivo.append(hash_padre)

            tree.append(livello_successivo)
            livello_corrente=livello_successivo

        merkle_root=tree[-1][0]

        # Generazione delle Merkle Proofs per ogni H(C_v)
        # La prova è la lista degli hash "fratelli" necessari per risalire alla radice
        proofs_per_elettore={}
        for indice_foglia,hash_foglia in enumerate(foglie):
            prova=[]
            indice_corrente=indice_foglia

            # Risaliamo l'albero livello per livello (escludendo la radice)
            for livello in range(len(tree)-1):
                nodi_livello=tree[livello]

                if indice_corrente%2==1: #è figlio destro
                    indice_fratello=indice_corrente-1
                    direzione="LEFT"
                else:
                    indice_fratello=indice_corrente+1
                    direzione="RIGHT"

                # Gestione del nodo duplicato dispari
                if indice_fratello<len(nodi_livello):
                    fratello=nodi_livello[indice_fratello]
                else:
                    fratello=nodi_livello[indice_corrente]

                prova.append({"sibling_hash":fratello,"direction":direzione})
                indice_corrente = indice_corrente // 2 # Saliamo al padre

            # Salviamo la prova associandola all'hash esadecimale del voto
            proofs_per_elettore[hash_foglia.hex()]=prova

        print(f"  [AE] Merkle Tree generato. Root: {merkle_root.hex()[:16]}...")
        return merkle_root, proofs_per_elettore

    def ricostruisci_chiave(self,custodi_presenti,quorum):
        if custodi_presenti>=quorum:
            self.chiave_ricostruita=True
            print("  [AE] Threshold Scheme: Chiave ricostruita con successo dai custodi.")
        else:
            raise Exception("Quorum non raggiunto per decifrare l'urna!")

    def spoglio_e_aggregazione(self):
        if not self.chiave_ricostruita:
            raise Exception("La chiave non è stata ricostruita!")

        print(f"  [AE] Avvio Shuffling di {len(self.urna)} schede...")
        random.shuffle(self.urna)

        risultati={"A":0,"B":0,"C":0,"Bianca":0}

        for cv in self.urna:
            plaintext=self.private_key1.decrypt(
                cv,
                padding.OAEP(
                    mgf=padding.MGF1(algorithm=hashes.SHA256()),
                    algorithm=hashes.SHA256(),
                    label=None
                )
            )
            voto = plaintext.decode().split("||")[0] # Estrae il voto ignorando padding e timestamp
            if voto in risultati:
                risultati[voto]+=1
        return risultati

class Elettore:
    def __init__(self, cf):
        self.cf=cf
        self.token_ar=None
        self.certificato=None
        self.ricevuta_voto=None
        self.private_key=None
        self.public_key=None

    def genera_chiavi(self):
        self.private_key=rsa.generate_private_key(public_exponent=65537,key_size=2048)
        self.public_key=self.private_key.public_key()

    def risolvi_challenge_ae(self,nonce):
        # L'elettore usa la sua SK_E in locale per firmare il Nonce
        firma=self.private_key.sign(
            nonce,
            padding.PSS(mgf=padding.MGF1(hashes.SHA256()), salt_length=padding.PSS.MAX_LENGTH),
            hashes.SHA256()
        )
        return firma

    def cifra_voto(self,pk_ae,voto):
        # Padding manuale per OAEP per nascondere il voto
        padding_casuale=os.urandom(16).hex()
        messaggio=f"{voto}||{padding_casuale}||{str(int(time.time()))}".encode()

        cv=pk_ae.encrypt(
            messaggio,
            padding.OAEP(
                mgf=padding.MGF1(algorithm=hashes.SHA256()),
                algorithm=hashes.SHA256(),
                label=None
            )
        )
        return cv

    def verifica_ricevuta(self,ricevuta,pk_ae):
        h_cv=sha256(ricevuta["cv"])
        dati_da_verificare=h_cv+ricevuta["timestamp"].encode()

        try:
          pk_ae.verify(
            ricevuta["firma"],
            dati_da_verificare,
            padding.PSS(mgf=padding.MGF1(hashes.SHA256()), salt_length=padding.PSS.MAX_LENGTH),
            hashes.SHA256()
          )
          print("  [E] Ricevuta verificata e valida!")
        except InvalidSignature:
            raise Exception("  [E] La ricevuta del voto non coincide!")

    def verifica_merkle_proof(self,prova,merkle_root):
        hash=sha256(self.ricevuta_voto["cv"])

        for step in prova:
          fratello=step["sibling_hash"]
          direzione=step["direction"]

          # L'ordine di concatenazione è vitale per l'hash
          if direzione=="LEFT":
            hash=sha256(fratello+hash)
          else: # RIGHT
            hash=sha256(hash+fratello)

        # Alla fine della risalita, l'hash calcolato deve essere identico alla Root dell'AE
        return hash==merkle_root

# ==========================================
# ESECUZIONE DELLA SIMULAZIONE E METRICHE WP4
# ==========================================

def run_simulation():
    print("=== INIZIO SIMULAZIONE SISTEMA E-VOTING ===")

    ar=AutoritaRegistrazione()
    ae=AutoritaElettorale()
    elettore=Elettore("RSSMRA80A01H501U")

    print("\n[FASE 1] -> REGISTRAZIONE & KEY DISTRIBUTION")
    print("----------------------------------------------------------------------")

    ae.inserisci_in_lista(elettore.cf)
    elettore.token_ar=ar.registra_avente_diritto(elettore.cf)
    print(f"  [AR]:Token Out-of-band generato e inviato per posta: {elettore.token_ar}")
    elettore.genera_chiavi()
    print("  [Client]: Generata nuova coppia di chiavi effimere per la sessione di voto (PK_E, SK_E).")
    elettore.certificato=ar.valida_e_rilascia_certificato(elettore.cf, elettore.token_ar, elettore.public_key)

    print("\n[FASE 2] -> AUTENTICAZIONE e VERIFICA DEL DIRITTO AL VOTO")
    print("----------------------------------------------------------------------")

    ae.set_lista_elettorale(ar.get_lista())
    nonce=ae.autentica_con_certificato(elettore.certificato, ar.public_key)
    firma_e=elettore.risolvi_challenge_ae(nonce)
    session_token=ae.verifica_nonce(nonce, firma_e, elettore.certificato)
    if session_token:
      print("  Elettore autenticato, Session Token rilasciato.")
      print("\n[FASE 3] -> ESPRESSIONE DEL VOTO e CRITTOGRAFIA DI SESSIONE")
      print("----------------------------------------------------------------------")
      #Misura Tempo di Cifratura (Costo Computazionale Client)
      start_time=time.perf_counter()
      cv=elettore.cifra_voto(ae.public_key1,"A")
      end_time=time.perf_counter()
      tempo_cifratura_ms=(end_time-start_time)*1000

      # WP4: Misura Dimensione Messaggio
      dimensione_cv=sys.getsizeof(cv)

      print(f"  [METRICA WP4 - Client]: Voto cifrato (OAEP) in {tempo_cifratura_ms:.2f} ms")
      print(f"  [METRICA WP4 - Network]: Dimensione del crittogramma inviato: {dimensione_cv} bytes")

      # Invio Voto
      elettore.ricevuta_voto=ae.ricevi_voto(session_token,cv)
      print(f"  Voto ricevuto. Hash Ricevuta: {elettore.ricevuta_voto["cv"].hex()[:16]}...")

      #Verifica ricevuta corretta
      elettore.verifica_ricevuta(elettore.ricevuta_voto, ae.public_key2)
      print(f"  [AE -> Client]: Voto inserito nell'urna digitale. Ricevuta emessa.")

    # Popoliamo l'urna con dei voti fittizi per misurare i tempi di spoglio
    print("\n  [SIMULAZIONE] Inserimento di 99 voti aggiuntivi nell'urna...")
    for _ in range(99):
        voto_random=random.choice(["A", "B", "C", "Bianca"])
        cv_fake=elettore.cifra_voto(ae.public_key1, voto_random)
        ae.urna.append(cv_fake)

    print("\n[FASE 4] -> AUDITING PUBBLICO & VERIFICABILITÀ")
    print("----------------------------------------------------------------------")
    print("  === Creazione merke tree ===")

    start_time=time.perf_counter()
    merkle_root,merkle_proofs=ae.genera_merkle_tree_e_proofs()
    end_time=time.perf_counter()
    tempo_creazione_MT=(end_time-start_time)*1000
    print(f"  [METRICA WP4 - Server]: Tempo di creazione del Merkle Tree: {tempo_creazione_MT:.2f}ms")

    print("\n  === Verifica individuale ===")

    start_time=time.perf_counter()
    if elettore.verifica_merkle_proof(merkle_proofs[sha256(elettore.ricevuta_voto["cv"]).hex()], merkle_root):
      print("  [SUCCESS]: Voto verificato e presente nel Merkle Tree")
    else:
      print("  [ERROR]: Voto NON presente nel Merkle tree")
    end_time=time.perf_counter()
    tempo_verifica_MP=(end_time-start_time)*1000
    print(f"  [METRICA WP4 - Client]: Tempo di verifica della Merkle Proof: {tempo_verifica_MP:.2f}ms")

    print("\n[FASE 5] -> APERTURA URNA, SHUFFLING E CONTEGGIO DEI VOTI")
    print("----------------------------------------------------------------------")
    ae.ricostruisci_chiave(5,3)

    # WP4: Misura Tempo di Spoglio (Costo Computazionale Server)
    start_time=time.perf_counter()
    risultati_finali=ae.spoglio_e_aggregazione()
    end_time=time.perf_counter()
    tempo_spoglio_s=(end_time-start_time)

    print("\n----------------------------------------------------------------------")
    print("             PUBBLICAZIONE DEI RISULTATI ELETTORALI PUBBLICI          ")
    print("----------------------------------------------------------------------")
    print(f"  Esito dello Scrutinio: {risultati_finali}")
    print(f"  [METRICA WP4 - Server Total]: Tempo totale di Mixnet Shuffling e Spoglio")
    print(f"                                per {len(ae.urna)} schede: {tempo_spoglio_s:.4f} secondi.")
    print("----------------------------------------------------------------------\n")
if __name__=="__main__":
    run_simulation()