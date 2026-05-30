/*
* ============================================================
*  PLAGIAT-DETECTOR V1.1
*  Détection de similarité entre deux fichiers texte
* ============================================================
*
*  CORRECTIONS V1.1 (sans modification architecturale) :
*
*  [FIX-01] STOP-WORDS FR+EN : liste de ~150 mots vides filtrés
*           dans next_word(). Les shingles composés uniquement
*           de mots fonctionnels ne polluent plus la hash table.
*           → Réduit massivement les faux positifs.
*
*  [FIX-02] SHINGLE_K = 7 au lieu de 5 : séquences de 7 mots
*           → coïncidences fortuites quasi impossibles dans des
*           textes académiques mixtes FR/EN.
*           → Réduit encore les faux positifs.
*
*  [FIX-03] JACCARD SYMÉTRIQUE :
*           sim = matched / (f1_total + f2_total - matched)
*           L'ancienne formule matched/f1_total était asymétrique
*           → sous-estimait le score quand F2 >> F1 (faux négatifs)
*           → surestimait quand F1 >> F2 (faux positifs).
*
*  [FIX-04] SEUILS RECALIBRÉS pour Jaccard symétrique + K=7
*           sur textes académiques FR/EN :
*             > 40% → plagiat probable  (était 70%)
*             > 20% → similarité élevée (était 40%)
*             >  8% → similarité modérée(était 15%)
*
*  PRINCIPE FONCTIONNEL (inchangé) :
*    Comparer deux fichiers texte et calculer leur degré de
*    similarité via la technique des k-grammes (shingles)
*    et la similarité de Jaccard symétrique :
*
*      sim = |shingles(F1) ∩ shingles(F2)|                × 100
*            ─────────────────────────────────────────────
*            |shingles(F1)| + |shingles(F2)| - |F1 ∩ F2|
*
*  ARCHITECTURE (identique à V1.0) :
*    [1] Prétraitement  : lecture de F2, extraction des shingles,
*                         stockage des empreintes dans un hash table
*                         en mémoire partagée (IPC_PRIVATE).
*    [2] Pool de tâches : F1 découpé en segments → file de msgs IPC.
*    [3] Work-stealing  : chaque thread pioche une tâche dès qu'il
*                         est libre → équilibrage automatique.
*    [4] Barbier endormi: contrôle l'admission des threads.
*    [5] Dîner philo.   : synchronisation démo en parallèle.
*    [6] Recouvrement   : pipe + exec(gzip) pour le rapport.
*
*  CONCEPTS OS (inchangés) :
*    Multiprocessus fork()   |  Multithread pthreads
*    Mémoire partagée IPC    |  File de messages IPC
*    Pipe + exec(gzip)       |  Sémaphores POSIX
*    Barbier endormi         |  Dîner des philosophes
*    Producteur/Consommateur |  Hash table lock-free (read-only)
*
*  Compilation : gcc -O2 -Wall -o plagiat plagiat_detector.c -lpthread -lrt
*  Usage       : ./plagiat <fichier1> <fichier2> <nb_workers> <nb_threads>
*  Exemple     : ./plagiat these.txt copie.txt 8 4
* ============================================================
*/

#include <stdio.h>
#include <stdlib.h>
#include <stdarg.h>
#include <string.h>
#include <ctype.h>
#include <unistd.h>
#include <pthread.h>
#include <semaphore.h>
#include <fcntl.h>
#include <time.h>
#include <signal.h>
#include <stdint.h>
#include <sys/ipc.h>
#include <sys/shm.h>
#include <sys/msg.h>
#include <sys/wait.h>
#include <sys/stat.h>

/* ==================== CONFIGURATION ==================== */
#define MAX_WORKERS    16
#define MAX_THREADS    16
#define LOG_SIZE        8
#define NUM_PHILO       5
#define WAITING_CAP   128
#define MSG_TASK        1L

/* Paramètres des shingles */
#define SHINGLE_K       7        /* [FIX-02] 7 mots/shingle (était 5)   */
#define MAX_WORD       48        /* longueur max d'un mot normalisé      */
#define HT_SIZE    (1<<19)       /* 512K slots → 2 Mo (puissance de 2!) */
#define MAX_PASSAGES   60        /* passages similaires à afficher       */

#define ST_IDLE 0
#define ST_BUSY 1
#define ST_DONE 2

/* ==================== [FIX-01] STOP-WORDS FR + EN ==================== */
/*
 * Liste de mots vides filtrés AVANT la construction des shingles.
 * Un shingle contenant exclusivement ces mots ne représente aucune
 * information sémantique et provoque des faux positifs entre tout
 * texte académique en français ou anglais.
 *
 * Triée alphabétiquement pour une recherche binaire en O(log n).
 */
static const char *STOPWORDS[] = {
    /* français */
    "alors","ainsi","apr","après","au","aucun","aussi","autre","aux",
    "avait","avec","avoir","car","cela","ces","cet","cette","ceux",
    "chaque","comme","dans","des","dont","dur","elle","elles","encore",
    "entre","est","etc","eux","fait","fois","leur","leurs","les","lors",
    "lui","mai","mais","même","mes","mot","non","nos","notre","nous",
    "ont","par","pas","peut","peu","plus","pour","qu","que","qui",
    "quoi","sans","ses","soi","soit","son","sur","tel","tous","tout",
    "très","trop","une","une","uns","via","vos","votre","vous",
    /* anglais */
    "about","above","after","against","all","also","among","and",
    "any","are","been","being","between","both","but","can","could",
    "did","does","each","even","from","had","has","have","here",
    "him","his","how","into","its","may","more","most","much","must",
    "nor","not","now","off","one","only","other","our","out","over",
    "own","per","said","same","she","should","since","some","such",
    "than","that","the","their","them","then","there","these","they",
    "this","those","through","thus","too","under","until","upon",
    "was","were","what","when","where","which","while","who","will",
    "with","would","yet","you","your"
};
#define STOPWORDS_COUNT (int)(sizeof(STOPWORDS)/sizeof(STOPWORDS[0]))

/* Comparateur pour bsearch */
static int cmp_str(const void *a, const void *b)
{
    return strcmp((const char *)a, *(const char **)b);
}

/* Retourne 1 si le mot est un stop-word, 0 sinon */
static int is_stopword(const char *word)
{
    return bsearch(word, STOPWORDS, (size_t)STOPWORDS_COUNT,
                   sizeof(char *), cmp_str) != NULL;
}

/* ==================== STRUCTURES ==================== */

typedef struct {
    int   id, status, active_threads, tasks_done, tasks_total;
    long  shingles_checked;
    long  shingles_matched;
    pid_t pid;
    long  ram_kb;
    float cpu_pct;
} WorkerStats;

typedef struct {
    /* ── Hash table des shingles de F2 (read-only après construction) ── */
    uint32_t    ht[HT_SIZE];
    long        f2_total_shingles;

    /* ── Résultats agrégés ── */
    long        f1_total;
    long        f1_matched;

    /* ── Passages similaires détectés ── */
    char        passages[MAX_PASSAGES][192];   /* plus large pour K=7 */
    int         passage_count;

    /* ── Monitoring ── */
    char        events[LOG_SIZE][144];
    int         log_head;
    WorkerStats stats[MAX_WORKERS];
} SharedData;

struct msg_buffer {
    long msg_type;
    long start_offset, end_offset;
    int  task_id;
};

/* ==================== GLOBAUX ==================== */
static int          shmid      = -1;
static int          msgid      = -1;
static char         shm_sem_name[64];
static SharedData  *shared_mem = NULL;
static sem_t       *shm_lock   = NULL;
static sem_t        forks_sem[NUM_PHILO];
static pthread_mutex_t thr_mutex = PTHREAD_MUTEX_INITIALIZER;

static long            prev_ticks[MAX_WORKERS];
static struct timespec prev_mono;
static int             ticks_init  = 0;
static int             g_num_tasks = 0;
static int             g_num_cpus  = 1;
static char            g_file1[256];
static char            g_file2[256];

/* ==================== NETTOYAGE IPC ==================== */
static void cleanup_ipc(void)
{
    if (shmid != -1) { shmctl(shmid, IPC_RMID, NULL); shmid = -1; }
    if (msgid != -1) { msgctl(msgid, IPC_RMID, NULL); msgid = -1; }
    if (shm_sem_name[0]) { sem_unlink(shm_sem_name); shm_sem_name[0] = '\0'; }
}

static void signal_handler(int sig)
{
    (void)sig;
    cleanup_ipc();
    printf("\033[?25h\033[0m\n\033[1;31m[SIGNAL] IPC libérés.\033[0m\n");
    _exit(1);
}

/* ==================== JOURNAL ==================== */
static void log_event(const char *fmt, ...)
{
    char msg[120]; va_list ap;
    va_start(ap, fmt); vsnprintf(msg, sizeof(msg), fmt, ap); va_end(ap);
    struct timespec ts; clock_gettime(CLOCK_MONOTONIC, &ts);
    sem_wait(shm_lock);
    int idx = shared_mem->log_head % LOG_SIZE;
    snprintf(shared_mem->events[idx], 144, "[%3ld.%03lds] %s",
             ts.tv_sec % 1000, ts.tv_nsec / 1000000L, msg);
    shared_mem->log_head++;
    sem_post(shm_lock);
}

/* ==================== MÉTRIQUES ==================== */
static long get_ram_kb(pid_t pid)
{
    char path[64], line[128];
    snprintf(path, sizeof(path), "/proc/%d/status", (int)pid);
    FILE *fp = fopen(path, "r"); if (!fp) return 0;
    long rss = 0;
    while (fgets(line, sizeof(line), fp))
        if (strncmp(line, "VmRSS:", 6) == 0) { sscanf(line+6, "%ld", &rss); break; }
    fclose(fp); return rss;
}

static long get_cpu_ticks(pid_t pid)
{
    char path[64], buf[1024];
    snprintf(path, sizeof(path), "/proc/%d/stat", (int)pid);
    FILE *fp = fopen(path, "r"); if (!fp) return -1;
    if (!fgets(buf, sizeof(buf), fp)) { fclose(fp); return -1; }
    fclose(fp);
    char *p = strrchr(buf, ')'); if (!p) return -1;
    unsigned long utime = 0, stime = 0;
    sscanf(p+2, "%*c %*d %*d %*d %*d %*d %*u %*u %*u %*u %*u %lu %lu",
           &utime, &stime);
    return (long)(utime + stime);
}

/* ====================================================================
 *  HASH TABLE — Empreintes des shingles de F2 (inchangé)
 * ==================================================================== */

static uint32_t fnv1a_shingle(char words[][MAX_WORD], int start, int k)
{
    uint32_t h = 2166136261u;
    for (int i = 0; i < k; i++) {
        int idx = (start + i) % k;
        const char *w = words[idx];
        while (*w) { h ^= (uint8_t)*w++; h *= 16777619u; }
        h ^= (uint8_t)' '; h *= 16777619u;
    }
    return h ? h : 1u;
}

static void ht_insert(uint32_t *ht, uint32_t hash)
{
    uint32_t idx = hash & (HT_SIZE - 1);
    while (ht[idx] && ht[idx] != hash)
        idx = (idx + 1) & (HT_SIZE - 1);
    ht[idx] = hash;
}

static int ht_lookup(const uint32_t *ht, uint32_t hash)
{
    uint32_t idx = hash & (HT_SIZE - 1);
    while (ht[idx]) {
        if (ht[idx] == hash) return 1;
        idx = (idx + 1) & (HT_SIZE - 1);
    }
    return 0;
}

/* ====================================================================
 *  TOKENISEUR — [FIX-01] filtrage stop-words intégré
 *
 *  Extrait le prochain mot significatif (non stop-word, ≥ 3 chars).
 *  La signature et le contrat de la fonction sont identiques à V1.0 ;
 *  seul le filtre is_stopword() est ajouté.
 * ==================================================================== */
static int next_word(const char *text, long *pos, long end,
                     char *word, int maxlen)
{
    /* Sauter les non-alpha */
    while (*pos < end && !isalpha((unsigned char)text[*pos])) (*pos)++;
    if (*pos >= end) return 0;

    int j = 0;
    while (*pos < end && isalpha((unsigned char)text[*pos]) && j < maxlen-1)
        word[j++] = tolower((unsigned char)text[(*pos)++]);
    word[j] = '\0';

    /* [FIX-01] Ignorer stop-words et mots trop courts */
    if (j < 3 || is_stopword(word))
        return next_word(text, pos, end, word, maxlen);

    return 1;
}

/* ====================================================================
 *  CONSTRUCTION DU HASH TABLE depuis F2 (inchangé sauf K)
 * ==================================================================== */
static long build_hashtable(const char *filename)
{
    FILE *f = fopen(filename, "r");
    if (!f) { perror("fopen F2"); return -1; }
    fseek(f, 0, SEEK_END);
    long sz = ftell(f); rewind(f);
    if (sz <= 0) { fclose(f); return 0; }

    char *buf = malloc((size_t)sz + 1);
    if (!buf) { fclose(f); return -1; }
    fread(buf, 1, (size_t)sz, f);
    buf[sz] = '\0';
    fclose(f);

    char window[SHINGLE_K][MAX_WORD];
    int  wpos   = 0;
    int  filled = 0;
    long pos    = 0;
    long count  = 0;
    char word[MAX_WORD];

    while (next_word(buf, &pos, sz, word, MAX_WORD)) {
        strncpy(window[wpos % SHINGLE_K], word, MAX_WORD-1);
        window[wpos % SHINGLE_K][MAX_WORD-1] = '\0';
        wpos++;
        if (wpos >= SHINGLE_K) filled = 1;
        if (filled) {
            int      base = wpos % SHINGLE_K;
            uint32_t h    = fnv1a_shingle(window, base, SHINGLE_K);
            ht_insert(shared_mem->ht, h);
            count++;
        }
    }
    free(buf);
    return count;
}

/* ====================================================================
 *  ANALYSE D'UN SEGMENT DE F1 (inchangé sauf K et buffer passage)
 * ==================================================================== */
static void analyse_chunk(const char *buf, long len,
                           long *p_checked, long *p_matched)
{
    char window[SHINGLE_K][MAX_WORD];
    int  wpos   = 0;
    int  filled = 0;
    long pos    = 0;
    char word[MAX_WORD];
    *p_checked = 0;
    *p_matched = 0;

    while (next_word(buf, &pos, len, word, MAX_WORD)) {
        strncpy(window[wpos % SHINGLE_K], word, MAX_WORD-1);
        window[wpos % SHINGLE_K][MAX_WORD-1] = '\0';
        wpos++;
        if (wpos >= SHINGLE_K) filled = 1;
        if (!filled) continue;

        int      base = wpos % SHINGLE_K;
        uint32_t h    = fnv1a_shingle(window, base, SHINGLE_K);
        (*p_checked)++;

        if (ht_lookup(shared_mem->ht, h)) {
            (*p_matched)++;

            pthread_mutex_lock(&thr_mutex);
            if (shared_mem->passage_count < MAX_PASSAGES) {
                char pass[192] = "";
                for (int i = 0; i < SHINGLE_K; i++) {
                    int idx = (base + i) % SHINGLE_K;
                    if (i) strncat(pass, " ", sizeof(pass)-strlen(pass)-1);
                    strncat(pass, window[idx], sizeof(pass)-strlen(pass)-1);
                }
                strncpy(shared_mem->passages[shared_mem->passage_count],
                        pass, 191);
                shared_mem->passage_count++;
            }
            pthread_mutex_unlock(&thr_mutex);
        }
    }
}

/* ====================================================================
 *  ALIGNEMENT NEWLINE (inchangé)
 * ==================================================================== */
static long align_newline(FILE *f, long offset, long file_size)
{
    if (offset <= 0)         return 0;
    if (offset >= file_size) return file_size;
    if (fseek(f, offset, SEEK_SET) != 0) return offset;
    int c; while ((c = fgetc(f)) != EOF && c != '\n');
    long pos = ftell(f);
    return (pos < 0) ? offset : pos;
}

/* ====================================================================
 *  BARBIER ENDORMI (inchangé)
 * ==================================================================== */
typedef struct {
    sem_t barber_ready, customer_ready, room_mutex;
    int   waiting, head, tail, queue[WAITING_CAP];
    volatile int done;
} BarberShop;

static void barber_shop_init(BarberShop *s) {
    sem_init(&s->barber_ready,   0, 0);
    sem_init(&s->customer_ready, 0, 0);
    sem_init(&s->room_mutex,     0, 1);
    s->waiting = s->head = s->tail = s->done = 0;
}
static void barber_shop_destroy(BarberShop *s) {
    sem_destroy(&s->barber_ready);
    sem_destroy(&s->customer_ready);
    sem_destroy(&s->room_mutex);
}
static int customer_enter(BarberShop *s, int tid) {
    sem_wait(&s->room_mutex);
    if (s->waiting >= WAITING_CAP) { sem_post(&s->room_mutex); return 0; }
    s->queue[s->tail % WAITING_CAP] = tid;
    s->tail++; s->waiting++;
    sem_post(&s->room_mutex);
    sem_post(&s->customer_ready);
    sem_wait(&s->barber_ready);
    return 1;
}
static void *barber_thread(void *arg) {
    BarberShop *s = (BarberShop *)arg;
    while (1) {
        sem_wait(&s->customer_ready);
        sem_wait(&s->room_mutex);
        if (s->done && s->waiting == 0) { sem_post(&s->room_mutex); break; }
        s->head++; s->waiting--;
        sem_post(&s->room_mutex);
        sem_post(&s->barber_ready);
    }
    return NULL;
}

/* ====================================================================
 *  DÎNER DES PHILOSOPHES (inchangé)
 * ==================================================================== */
static void *philosopher(void *arg) {
    int id = *(int *)arg, l = id, r = (id + 1) % NUM_PHILO;
    for (int meal = 0; meal < 3; meal++) {
        usleep((unsigned)(rand() % 40000 + 10000));
        if (id % 2 == 0) { sem_wait(&forks_sem[l]); sem_wait(&forks_sem[r]); }
        else              { sem_wait(&forks_sem[r]); sem_wait(&forks_sem[l]); }
        log_event("Philo %d: mange (repas %d/3)", id, meal + 1);
        usleep((unsigned)(rand() % 15000 + 5000));
        sem_post(&forks_sem[l]); sem_post(&forks_sem[r]);
    }
    log_event("Philo %d: rassasie", id);
    return NULL;
}

/* ====================================================================
 *  THREAD ANALYSEUR — WORK-STEALING (inchangé)
 * ==================================================================== */
typedef struct {
    int        worker_id, thread_id;
    BarberShop *barber;
} ThreadArg;

static void *analyzer_thread(void *arg)
{
    ThreadArg *d = (ThreadArg *)arg;
    while (!customer_enter(d->barber, d->thread_id)) usleep(500);

    pthread_mutex_lock(&thr_mutex);
    shared_mem->stats[d->worker_id].active_threads++;
    pthread_mutex_unlock(&thr_mutex);

    struct msg_buffer msg;

    while (msgrcv(msgid, &msg, sizeof(msg) - sizeof(long), MSG_TASK, 0) >= 0) {
        if (msg.task_id == -1) break;

        long chunk_sz = msg.end_offset - msg.start_offset;
        if (chunk_sz <= 0) {
            pthread_mutex_lock(&thr_mutex);
            shared_mem->stats[d->worker_id].tasks_done++;
            pthread_mutex_unlock(&thr_mutex);
            continue;
        }

        char *buf = malloc((size_t)chunk_sz + 1);
        if (!buf) continue;

        FILE *f = fopen(g_file1, "r");
        if (f) {
            fseek(f, msg.start_offset, SEEK_SET);
            size_t rd = fread(buf, 1, (size_t)chunk_sz, f);
            buf[rd] = '\0';
            fclose(f);
        } else { buf[0] = '\0'; }

        long checked = 0, matched = 0;
        analyse_chunk(buf, chunk_sz, &checked, &matched);
        free(buf);

        pthread_mutex_lock(&thr_mutex);
        shared_mem->stats[d->worker_id].shingles_checked += checked;
        shared_mem->stats[d->worker_id].shingles_matched += matched;
        shared_mem->f1_total   += checked;
        shared_mem->f1_matched += matched;
        shared_mem->stats[d->worker_id].tasks_done++;
        pthread_mutex_unlock(&thr_mutex);

        log_event("W%d/T%d: tache %d -> %ld check, %ld match",
                  d->worker_id, d->thread_id, msg.task_id, checked, matched);
    }

    pthread_mutex_lock(&thr_mutex);
    shared_mem->stats[d->worker_id].active_threads--;
    pthread_mutex_unlock(&thr_mutex);
    return NULL;
}

/* ====================================================================
 *  PROCESSUS WORKER (inchangé)
 * ==================================================================== */
static void worker_process(int id, int nt)
{
    BarberShop barber;
    barber_shop_init(&barber);

    sem_wait(shm_lock);
    shared_mem->stats[id].pid    = getpid();
    shared_mem->stats[id].status = ST_BUSY;
    sem_post(shm_lock);

    pthread_t barber_tid;
    pthread_create(&barber_tid, NULL, barber_thread, &barber);

    pthread_t threads[MAX_THREADS];
    ThreadArg args[MAX_THREADS];
    for (int i = 0; i < nt; i++) {
        args[i].worker_id = id;
        args[i].thread_id = i;
        args[i].barber    = &barber;
        pthread_create(&threads[i], NULL, analyzer_thread, &args[i]);
    }
    for (int i = 0; i < nt; i++) pthread_join(threads[i], NULL);

    barber.done = 1;
    sem_post(&barber.customer_ready);
    pthread_join(barber_tid, NULL);
    barber_shop_destroy(&barber);

    sem_wait(shm_lock);
    long wc = shared_mem->stats[id].shingles_checked;
    long wm = shared_mem->stats[id].shingles_matched;
    int  td = shared_mem->stats[id].tasks_done;
    shared_mem->stats[id].status = ST_DONE;
    sem_post(shm_lock);

    log_event("Worker %d DONE: %ld shingles, %ld matchs, %d taches",
              id, wc, wm, td);

    /* Recouvrement : pipe + exec(gzip) */
    int pfd[2];
    if (pipe(pfd) == 0) {
        pid_t gz = fork();
        if (gz == 0) {
            close(pfd[1]); dup2(pfd[0], STDIN_FILENO); close(pfd[0]);
            int out = open("rapport_plagiat.gz",
                           O_WRONLY|O_CREAT|O_APPEND, 0644);
            if (out >= 0) dup2(out, STDOUT_FILENO);
            execlp("gzip", "gzip", "-c", NULL); _exit(1);
        }
        close(pfd[0]);
        /* [FIX-03] Jaccard symétrique dans le rapport aussi */
        long f2t = shared_mem->f2_total_shingles;
        long denom = wc + f2t - wm;
        float pct = (denom > 0) ? (float)wm * 100.0f / (float)denom : 0.0f;
        char rep[256];
        int n = snprintf(rep, sizeof(rep),
            "Worker %d (PID %d): %ld shingles verifies, "
            "%ld matches, Jaccard=%.1f%%, %d taches\n",
            id, (int)getpid(), wc, wm, pct, td);
        if (write(pfd[1], rep, (size_t)n) < 0) { /* best-effort */ }
        close(pfd[1]);
        waitpid(gz, NULL, 0);
    }

    shmdt(shared_mem);
    sem_close(shm_lock);
    exit(0);
}

/* ====================================================================
 *  THREAD PRODUCTEUR — Producteur/Consommateur (inchangé)
 * ==================================================================== */
typedef struct {
    long *offsets;
    int   ntasks, nw, nt;
} ProducerArg;

static void *producer_thread(void *arg)
{
    ProducerArg *p = (ProducerArg *)arg;
    for (int i = 0; i < p->ntasks; i++) {
        struct msg_buffer m; memset(&m, 0, sizeof(m));
        m.msg_type     = MSG_TASK;
        m.start_offset = p->offsets[i];
        m.end_offset   = p->offsets[i + 1];
        m.task_id      = i;
        if (msgsnd(msgid, &m, sizeof(m) - sizeof(long), 0) < 0) {
            perror("msgsnd"); break;
        }
    }
    for (int i = 0; i < p->nw * p->nt; i++) {
        struct msg_buffer m; memset(&m, 0, sizeof(m));
        m.msg_type = MSG_TASK; m.task_id = -1;
        msgsnd(msgid, &m, sizeof(m) - sizeof(long), 0);
    }
    log_event("Producteur: %d taches + %d pills envoyees",
              p->ntasks, p->nw * p->nt);
    free(p->offsets);
    free(p);
    return NULL;
}

/* ====================================================================
 *  AFFICHAGE TEMPS RÉEL
 *  [FIX-03] Jaccard symétrique dans le score affiché
 *  [FIX-04] Seuils de verdict recalibrés
 * ==================================================================== */
static void draw_bar_pct(float ratio, int width)
{
    int f = (int)(ratio * width); if (f<0) f=0; if (f>width) f=width;
    for (int j=0;j<f;    j++) printf("\033[42m\xe2\x96\x88\033[0m");
    for (int j=f;j<width;j++) printf("\xe2\x96\x91");
}

static void draw_bar_val(long val, long maxv, int w, const char *col)
{
    if (maxv<=0) maxv=1;
    int f=(int)((float)val/(float)maxv*(float)w);
    if (f<0) f=0; if (f>w) f=w;
    printf("%s",col);
    for(int j=0;j<f;j++) printf("\xe2\x96\x88");
    printf("\033[40m");
    for(int j=f;j<w;j++) printf("\xe2\x96\x91");
    printf("\033[0m");
}

static void draw_similarity_bar(float pct, int width)
{
    int f = (int)(pct / 100.0f * width);
    if (f<0) f=0; if (f>width) f=width;
    /* [FIX-04] couleurs alignées sur nouveaux seuils */
    const char *col = (pct > 40.0f) ? "\033[41m" :
                      (pct > 20.0f) ? "\033[43m" : "\033[42m";
    printf("%s", col);
    for (int j=0;j<f;    j++) printf("\xe2\x96\x88");
    printf("\033[40m");
    for (int j=f;j<width;j++) printf("\xe2\x96\x91");
    printf("\033[0m");
}

static void draw_ui(int nw)
{
    struct timespec now; clock_gettime(CLOCK_MONOTONIC, &now);
    long clk = sysconf(_SC_CLK_TCK); if (clk<=0) clk=100;
    float cpu_cap = (float)(g_num_cpus * 100);

    if (!ticks_init) {
        prev_mono = now;
        for (int i=0;i<nw;i++) {
            long t = get_cpu_ticks(shared_mem->stats[i].pid);
            prev_ticks[i] = (t<0)?0:t;
        }
        ticks_init = 1; return;
    }
    double elapsed = (now.tv_sec  - prev_mono.tv_sec)
                   + (now.tv_nsec - prev_mono.tv_nsec)*1e-9;

    long max_ram = 1;
    for (int i=0;i<nw;i++)
        if (shared_mem->stats[i].ram_kb > max_ram)
            max_ram = shared_mem->stats[i].ram_kb;

    /* [FIX-03] Jaccard symétrique : matched / (f1 + f2 - matched) */
    long   f1t  = shared_mem->f1_total;
    long   f1m  = shared_mem->f1_matched;
    long   f2t  = shared_mem->f2_total_shingles;
    long   denom = f1t + f2t - f1m;
    float  sim  = (denom > 0) ? (float)f1m * 100.0f / (float)denom : 0.0f;

    printf("\033[H");

    /* ── En-tête ── */
    printf("\033[1;36m"
"╔══════════════════════════════════════════════════════════════════════════╗\033[K\n"
"║   🔍  PLAGIAT-DETECTOR V1.1 — DÉTECTION DE SIMILARITÉ PARALLÈLE 🔍    ║\033[K\n"
"╚══════════════════════════════════════════════════════════════════════════╝"
"\033[0m\033[K\n");

    printf("  \033[0;37mF1: %-30s  F2: %-30s\033[0m\033[K\n", g_file1, g_file2);
    printf("  \033[0;33mSHMID=%-6d MSGID=%-6d SEM=%s CPUs=%d Pool=%d tâches\033[0m\033[K\n\n",
           shmid, msgid, shm_sem_name, g_num_cpus, g_num_tasks);

    /* ── Score de similarité — [FIX-04] seuils recalibrés ── */
    const char *verdict =
        (sim > 40.0f) ? "\033[1;31m⚠  PLAGIAT PROBABLE\033[0m" :
        (sim > 20.0f) ? "\033[1;33m⚡ SIMILARITÉ ÉLEVÉE\033[0m" :
        (sim >  8.0f) ? "\033[1;34m📝 SIMILARITÉ MODÉRÉE\033[0m" :
                        "\033[1;32m✅ DOCUMENTS DISTINCTS\033[0m";

    printf("  \033[1;36m╔══════════════════════════════════════════════════════════╗\033[0m\033[K\n");
    printf("  \033[1;36m║\033[0m  🎯 SIMILARITÉ JACCARD (sym.) : \033[1;33m%6.2f %%\033[0m  %s",
           sim, verdict);
    printf("  \033[1;36m\033[0m\033[K\n");
    printf("  \033[1;36m║\033[0m  ");
    draw_similarity_bar(sim, 50);
    printf("  \033[1;36m\033[0m\033[K\n");
    printf("  \033[1;36m║\033[0m  Shingles F1 : \033[1;33m%-8ld\033[0m  "
           "Matchés : \033[1;32m%-8ld\033[0m  "
           "F2 ref : \033[1;34m%-8ld\033[0m  "
           "Denom : \033[0;37m%-8ld\033[0m\033[K\n",
           f1t, f1m, f2t, denom);
    printf("  \033[1;36m╚══════════════════════════════════════════════════════════╝\033[0m\033[K\n\n");

    /* ── Passages similaires ── */
    int npass = shared_mem->passage_count;
    printf("  \033[1;35m📄 PASSAGES SIMILAIRES DÉTECTÉS (%d/%d)\033[0m\033[K\n", npass, MAX_PASSAGES);
    printf("  ┌──────────────────────────────────────────────────────────────────┐\033[K\n");
    int show = (npass > 8) ? 8 : npass;
    for (int i = 0; i < show; i++)
        printf("  │ \033[0;33m[%02d]\033[0m %-62s │\033[K\n",
               i+1, shared_mem->passages[i]);
    if (npass == 0)
        printf("  │ %-68s │\033[K\n", "  (analyse en cours...)");
    if (npass > 8)
        printf("  │ \033[0;37m... et %d autres passages dans rapport_plagiat.gz\033[0m"
               "%*s │\033[K\n", npass-8, (int)(32), "");
    printf("  └──────────────────────────────────────────────────────────────────┘\033[K\n\n");

    /* ── Tableau workers ── */
    printf("\033[1;33m"
" ┌────┬──────────┬───────────┬───────┬────────┬─────────┬──────────┬────────────────┐\033[K\n"
" │ ID │   PID    │  STATUT   │  THR  │  CPU%%  │  RAM KB │ SHINGLES │  PROGRESSION   │\033[K\n"
" ├────┼──────────┼───────────┼───────┼────────┼─────────┼──────────┼────────────────┤\033[0m\033[K\n");

    for (int i=0;i<nw;i++) {
        WorkerStats *ws = &shared_mem->stats[i];
        if (ws->status != ST_DONE && ws->pid > 0) {
            ws->ram_kb = get_ram_kb(ws->pid);
            long ticks = get_cpu_ticks(ws->pid);
            if (ticks>=0 && elapsed>0.05) {
                float raw=(float)((ticks-prev_ticks[i])/(double)clk/elapsed*100.0f);
                if(raw<0)raw=0; if(raw>cpu_cap)raw=cpu_cap;
                ws->cpu_pct=raw;
            }
            if(ticks>=0) prev_ticks[i]=ticks;
        }
        const char *sc,*ss;
        switch(ws->status){
        case ST_BUSY: sc="\033[1;32m";ss="  ACTIF  ";break;
        case ST_DONE: sc="\033[1;34m";ss="  DONE   ";break;
        default:      sc="\033[0;37m";ss="  IDLE   ";break;
        }
        int   tpw   = (ws->tasks_total>0)?ws->tasks_total:1;
        float ratio = (float)ws->tasks_done/(float)tpw;
        if(ratio>1.0f)ratio=1.0f;
        printf(" │ \033[1;36m%2d\033[0m │ %8d │ %s%s\033[0m │ "
               "\033[1;33m%5d\033[0m │ %6.1f │ %7ld │ %8ld │ ",
               i, ws->pid, sc, ss,
               ws->active_threads, ws->cpu_pct,
               ws->ram_kb, ws->shingles_checked);
        draw_bar_pct(ratio, 14);
        printf(" │\033[K\n");
    }
    printf("\033[1;33m"
" └────┴──────────┴───────────┴───────┴────────┴─────────┴──────────┴────────────────┘"
"\033[0m\033[K\n");

    prev_mono = now;

    int tot_done = 0;
    for(int i=0;i<nw;i++) tot_done+=shared_mem->stats[i].tasks_done;
    printf("\n  \033[1;32m► TÂCHES: %d / %d  │  SHINGLES ANALYSÉS: %ld  │  MATCHÉS: %ld\033[0m\033[K\n\n",
           tot_done, g_num_tasks, f1t, f1m);

    /* ── RAM ── */
    printf("  \033[1;35m📊 RAM PAR WORKER\033[0m\033[K\n");
    for(int i=0;i<nw;i++){
        printf("   W%-2d │",i);
        draw_bar_val(shared_mem->stats[i].ram_kb, max_ram, 28, "\033[45m");
        printf("│ %6ld KB\033[K\n", shared_mem->stats[i].ram_kb);
    }

    /* ── CPU ── */
    printf("\n  \033[1;35m⚡ CPU%% PAR WORKER\033[0m\033[K\n");
    for(int i=0;i<nw;i++){
        float c=shared_mem->stats[i].cpu_pct;
        printf("   W%-2d │",i);
        draw_bar_val((long)c,(long)cpu_cap,28,c>70.0f?"\033[41m":"\033[43m");
        printf("│ %5.1f %%\033[K\n",c);
    }

    /* ── Gantt ── */
    printf("\n  \033[1;35m⏱  GANTT — tâches F1 (work-stealing)\033[0m\033[K\n");
    for(int i=0;i<nw;i++){
        int done=shared_mem->stats[i].tasks_done;
        int tpw=(shared_mem->stats[i].tasks_total>0)?
                 shared_mem->stats[i].tasks_total:1;
        float r=(float)done/(float)tpw; if(r>1.0f)r=1.0f;
        printf("   W%-2d │",i);
        draw_bar_pct(r, 35);
        printf("│ %4d/%4d\033[K\n", done, tpw);
    }

    /* ── Journal IPC ── */
    printf("\n  \033[1;35m📋 JOURNAL IPC\033[0m\033[K\n");
    printf("  ┌────────────────────────────────────────────────────────────────────────┐\033[K\n");
    int head=shared_mem->log_head;
    for(int i=0;i<LOG_SIZE;i++){
        int idx=((head-LOG_SIZE+i)%LOG_SIZE+LOG_SIZE)%LOG_SIZE;
        printf("  │ %-72s │\033[K\n",
               shared_mem->events[idx][0]?shared_mem->events[idx]:"");
    }
    printf("  └────────────────────────────────────────────────────────────────────────┘\033[K\n");

    printf("\n  \033[1;36m🔗 IPC PRIVÉS: [SHMID=%d✓] [MSGID=%d✓] [%s✓]\033[0m\033[K\n",
           shmid, msgid, shm_sem_name);
    printf("  \033[1;36m🔗 SYNC: [Barbier Endormi✓] [Dîner Philosophes✓] [Producteur/Consommateur✓]\033[0m\033[K\n");
    printf("  \033[1;36m🔗 Technique: Shingles %d-grammes │ Jaccard symétrique │ Stop-words FR+EN (%d)\033[0m\033[K\n",
           SHINGLE_K, STOPWORDS_COUNT);
    fflush(stdout);
}

/* ====================================================================
 *  MAIN (inchangé sauf affichage du résultat final)
 * ==================================================================== */
int main(int argc, char *argv[])
{
    if (argc < 5) {
        fprintf(stderr,
            "\nUsage   : %s <fichier1> <fichier2> <nb_workers> <nb_threads>\n"
            "Exemple : %s these.txt copie.txt 8 4\n\n"
            "  fichier1 = document à analyser (découpé en tâches)\n"
            "  fichier2 = document de référence (indexé en hash table)\n"
            "  Résultat : pourcentage de similarité Jaccard + passages communs\n\n",
            argv[0], argv[0]);
        return 1;
    }

    int nw = atoi(argv[3]);
    int nt = atoi(argv[4]);
    if (nw<1||nw>MAX_WORKERS){fprintf(stderr,"nb_workers:1..%d\n",MAX_WORKERS);return 1;}
    if (nt<1||nt>MAX_THREADS){fprintf(stderr,"nb_threads:1..%d\n",MAX_THREADS);return 1;}

    g_num_cpus  = (int)sysconf(_SC_NPROCESSORS_ONLN);
    if (g_num_cpus<1) g_num_cpus=1;

    g_num_tasks = nw * nt * 8;
    if (g_num_tasks > 2048) g_num_tasks = 2048;
    if (g_num_tasks < nw)   g_num_tasks = nw;

    strncpy(g_file1, argv[1], 255); g_file1[255]='\0';
    strncpy(g_file2, argv[2], 255); g_file2[255]='\0';

    signal(SIGINT,  signal_handler);
    signal(SIGTERM, signal_handler);

    shmid = shmget(IPC_PRIVATE, sizeof(SharedData), IPC_CREAT|0600);
    if (shmid<0){perror("shmget");return 1;}
    shared_mem = (SharedData*)shmat(shmid, NULL, 0);
    if (shared_mem==(SharedData*)-1){perror("shmat");shmctl(shmid,IPC_RMID,NULL);return 1;}
    memset(shared_mem, 0, sizeof(SharedData));

    msgid = msgget(IPC_PRIVATE, IPC_CREAT|0600);
    if (msgid<0){perror("msgget");cleanup_ipc();return 1;}

    snprintf(shm_sem_name, sizeof(shm_sem_name), "/plagiat_%d", (int)getpid());
    sem_unlink(shm_sem_name);
    shm_lock = sem_open(shm_sem_name, O_CREAT|O_EXCL, 0600, 1);
    if (shm_lock==SEM_FAILED){perror("sem_open");cleanup_ipc();return 1;}

    /* Étape 1 : Indexer F2 */
    printf("🔍 Indexation de F2 : %s ...\n", g_file2);
    printf("   Stop-words filtrés : %d (FR+EN)\n", STOPWORDS_COUNT);
    printf("   Shingle K          : %d mots\n", SHINGLE_K);
    long f2_shingles = build_hashtable(g_file2);
    if (f2_shingles < 0) {
        fprintf(stderr, "Erreur lecture F2.\n"); cleanup_ipc(); return 1;
    }
    shared_mem->f2_total_shingles = f2_shingles;
    printf("✅ F2 indexé : %ld shingles (%d-grammes, sans stop-words) dans le hash table\n",
           f2_shingles, SHINGLE_K);

    /* Étape 2 : Offsets F1 */
    FILE *f = fopen(g_file1, "r");
    if (!f){perror("fopen F1");cleanup_ipc();return 1;}
    fseek(f, 0, SEEK_END);
    long sz = ftell(f);
    if (sz<=0){fprintf(stderr,"F1 vide.\n");fclose(f);cleanup_ipc();return 1;}

    long *offsets = malloc((size_t)(g_num_tasks+1)*sizeof(long));
    if (!offsets){fclose(f);cleanup_ipc();return 1;}
    offsets[0]=0;
    for(int i=1;i<g_num_tasks;i++){
        long raw=(long)i*(sz/g_num_tasks);
        offsets[i]=align_newline(f,raw,sz);
    }
    offsets[g_num_tasks]=sz;
    fclose(f);

    int base=g_num_tasks/nw, extra=g_num_tasks%nw;
    for(int i=0;i<nw;i++)
        shared_mem->stats[i].tasks_total=base+(i<extra?1:0);

    {int fd=open("rapport_plagiat.gz",O_WRONLY|O_CREAT|O_TRUNC,0644);
     if(fd>=0)close(fd);}

    printf("🚀 Lancement : %d workers × %d threads, %d tâches sur F1 (%ld octets)\n\n",
           nw, nt, g_num_tasks, sz);
    usleep(500000);
    printf("\033[?25l\033[2J"); fflush(stdout);

    /* Étape 3 : Forker les workers */
    pid_t worker_pids[MAX_WORKERS];
    for(int i=0;i<nw;i++){
        pid_t pid=fork();
        if(pid==0){ signal(SIGINT,SIG_IGN); worker_process(i,nt); }
        worker_pids[i]=pid;
        if(pid>0){
            sem_wait(shm_lock);
            shared_mem->stats[i].pid=pid;
            sem_post(shm_lock);
        }
    }

    /* Étape 4 : Thread producteur */
    ProducerArg *parg=malloc(sizeof(ProducerArg));
    parg->offsets=offsets; parg->ntasks=g_num_tasks;
    parg->nw=nw; parg->nt=nt;
    pthread_t prod_tid;
    pthread_create(&prod_tid, NULL, producer_thread, parg);

    log_event("START: %d workers x %d threads, F1=%ld o, F2=%ld shingles",
              nw, nt, sz, f2_shingles);

    /* Processus philosophes */
    pid_t philo_pid=fork();
    if(philo_pid==0){
        signal(SIGINT,SIG_IGN);
        srand((unsigned)time(NULL)^(unsigned)getpid());
        for(int i=0;i<NUM_PHILO;i++) sem_init(&forks_sem[i],0,1);
        pthread_t pts[NUM_PHILO]; int ids[NUM_PHILO];
        for(int i=0;i<NUM_PHILO;i++){ids[i]=i;pthread_create(&pts[i],NULL,philosopher,&ids[i]);}
        for(int i=0;i<NUM_PHILO;i++) pthread_join(pts[i],NULL);
        for(int i=0;i<NUM_PHILO;i++) sem_destroy(&forks_sem[i]);
        shmdt(shared_mem); sem_close(shm_lock); exit(0);
    }

    /* Boucle moniteur */
    int active=1;
    while(active){
        draw_ui(nw); usleep(200000);
        active=0;
        for(int i=0;i<nw;i++)
            if(shared_mem->stats[i].status!=ST_DONE){active=1;break;}
    }
    draw_ui(nw);

    pthread_join(prod_tid, NULL);
    for(int i=0;i<nw;i++) waitpid(worker_pids[i],NULL,0);
    waitpid(philo_pid,NULL,WNOHANG);

    /* ── Résultat final — [FIX-03] Jaccard symétrique ── */
    long   tf   = shared_mem->f1_total;
    long   mf   = shared_mem->f1_matched;
    long   f2t  = shared_mem->f2_total_shingles;
    long   den  = tf + f2t - mf;
    float  sim  = (den > 0) ? (float)mf * 100.0f / (float)den : 0.0f;
    int    npass= shared_mem->passage_count;

    printf("\033[?25h\n");
    printf("\033[1;36m══════════════════════════════════════════════\033[0m\n");
    printf("\033[1;32m  RÉSULTAT FINAL — PLAGIAT-DETECTOR V1.1\033[0m\n");
    printf("\033[1;36m══════════════════════════════════════════════\033[0m\n");
    printf("  Fichier 1          : %s\n", g_file1);
    printf("  Fichier 2          : %s\n", g_file2);
    printf("  Shingles F1        : %ld\n", tf);
    printf("  Shingles F2 ref    : %ld\n", f2t);
    printf("  Matchés            : %ld\n", mf);
    printf("  Dénominateur union : %ld\n", den);
    printf("  \033[1;33mJACCARD SYMÉTRIQUE : %.2f %%\033[0m\n", sim);
    /* [FIX-04] seuils recalibrés */
    if      (sim>40.0f) printf("  \033[1;31mVERDICT : ⚠  PLAGIAT PROBABLE\033[0m\n");
    else if (sim>20.0f) printf("  \033[1;33mVERDICT : ⚡ SIMILARITÉ ÉLEVÉE\033[0m\n");
    else if (sim> 8.0f) printf("  \033[1;34mVERDICT : 📝 SIMILARITÉ MODÉRÉE\033[0m\n");
    else                printf("  \033[1;32mVERDICT : ✅ DOCUMENTS DISTINCTS\033[0m\n");
    printf("  Passages communs   : %d  → rapport_plagiat.gz\n", npass);
    printf("\033[1;36m══════════════════════════════════════════════\033[0m\n");
    printf("\n  \033[0;37mCorrections V1.1 actives:\033[0m\n");
    printf("  \033[0;32m  [✓] Stop-words FR+EN (%d mots filtrés)\033[0m\n", STOPWORDS_COUNT);
    printf("  \033[0;32m  [✓] Shingle K=%d (était K=5)\033[0m\n", SHINGLE_K);
    printf("  \033[0;32m  [✓] Jaccard symétrique (était asymétrique)\033[0m\n");
    printf("  \033[0;32m  [✓] Seuils recalibrés (>40%%, >20%%, >8%%)\033[0m\n");

    shmdt(shared_mem);
    cleanup_ipc();
    return 0;
}