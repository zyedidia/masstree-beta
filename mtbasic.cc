/* Masstree
 * Eddie Kohler, Yandong Mao, Robert Morris
 * Copyright (c) 2012-2014 President and Fellows of Harvard College
 * Copyright (c) 2012-2014 Massachusetts Institute of Technology
 *
 * Permission is hereby granted, free of charge, to any person obtaining a
 * copy of this software and associated documentation files (the "Software"),
 * to deal in the Software without restriction, subject to the conditions
 * listed in the Masstree LICENSE file. These conditions include: you must
 * preserve this copyright notice, and you cannot mention the copyright
 * holders in advertising related to the Software without their permission.
 * The Software is provided WITHOUT ANY WARRANTY, EXPRESS OR IMPLIED. This
 * notice is a summary of the Masstree LICENSE file; the license in that file
 * is legally binding.
 */
// -*- mode: c++ -*-
// mtd: key/value server
//

#include <chrono>
#include <stdio.h>
#include <stdarg.h>
#include <ctype.h>
#include <stdlib.h>
#include <unistd.h>
#include <sys/socket.h>
#include <netinet/in.h>
#include <netinet/tcp.h>
#include <sys/select.h>
#include <sys/mman.h>
#include <sys/stat.h>
#include <limits.h>
#if HAVE_SYS_EPOLL_H
#include <sys/epoll.h>
#endif
#if __linux__
#include <asm-generic/mman.h>
#endif
#include <fcntl.h>
#include <assert.h>
#include <string.h>
#include <pthread.h>
#include <math.h>
#include <signal.h>
#include <errno.h>
#ifdef __linux__
#include <malloc.h>
#endif
#include "nodeversion.hh"
#include "kvstats.hh"
#include "json.hh"
#include "kvtest.hh"
#include "kvrandom.hh"
#include "clp.h"
#include "log.hh"
#include "checkpoint.hh"
#include "file.hh"
#include "kvproto.hh"
#include "query_masstree.hh"
#include "masstree_tcursor.hh"
#include "masstree_insert.hh"
#include "masstree_remove.hh"
#include "masstree_scan.hh"
#include "msgpack.hh"
#include <algorithm>
#include <deque>
using lcdf::StringAccum;

enum { CKState_Quit, CKState_Uninit, CKState_Ready, CKState_Go };

volatile bool timeout[2] = {false, false};
double duration[2] = {10, 0};

Masstree::default_table *tree;

kvepoch_t global_log_epoch = 0;
// all default to the number of cores
static int udpthreads = 0;
static int tcpthreads = 0;
static int nckthreads = 0;
static int testthreads = 0;
static int nlogger = 0;
static std::vector<int> cores;

static bool logging = true;
static bool pinthreads = false;
static bool recovery_only = false;
volatile uint64_t globalepoch = 1;     // global epoch, updated by main thread regularly
volatile uint64_t active_epoch = 1;
static int port = 2117;
static uint64_t test_limit = ~uint64_t(0);
static int doprint = 0;
int kvtest_first_seed = 31949;

static volatile sig_atomic_t go_quit = 0;
static int quit_pipe[2];

static std::vector<const char*> logdirs;
static std::vector<const char*> ckpdirs;

static logset* logs;
volatile bool recovering = false; // so don't add log entries, and free old value immediately

static double checkpoint_interval = 1000000;
static kvepoch_t ckp_gen = 0; // recover from checkpoint
static ckstate *cks = NULL; // checkpoint status of all checkpointing threads
static pthread_cond_t rec_cond;
pthread_mutex_t rec_mu;
static int rec_nactive;
static int rec_state = REC_NONE;

kvtimestamp_t initial_timestamp;

static pthread_cond_t checkpoint_cond;
static pthread_mutex_t checkpoint_mu;

static void prepare_thread(threadinfo *ti);
static int* tcp_thread_pipes;
static void* tcp_threadfunc(void* ti);
static void* udp_threadfunc(void* ti);

static void log_init();
static void recover(threadinfo*);
static kvepoch_t read_checkpoint(threadinfo*, const char *path);

static void* conc_checkpointer(void* ti);
static void recovercheckpoint(threadinfo* ti);

static void *canceling(void *);
static void catchint(int);
static void epochinc(int);

struct kvtest_client {
    kvtest_client()
        : checks_(0), kvo_() {
    }
    kvtest_client(const char *testname)
        : testname_(testname), checks_(0), kvo_() {
    }

    int id() const {
        return ti_->index();
    }
    int nthreads() const {
        return testthreads;
    }
    void set_thread(threadinfo *ti) {
        ti_ = ti;
    }
    void register_timeouts(int n) {
        always_assert(n <= (int) arraysize(::timeout));
        for (int i = 1; i < n; ++i)
            if (duration[i] == 0)
                duration[i] = 0;//duration[i - 1];
    }
    bool timeout(int which) const {
        return ::timeout[which];
    }
    uint64_t limit() const {
        return test_limit;
    }
    Json param(const String&) const {
        return Json();
    }
    double now() const {
        return ::now();
    }

    void get(long ikey, Str *value);
    void get(const Str &key);
    void get(long ikey) {
        quick_istr key(ikey);
        get(key.string());
    }
    void get_check(const Str &key, const Str &expected);
    void get_check(const char *key, const char *expected) {
        get_check(Str(key, strlen(key)), Str(expected, strlen(expected)));
    }
    void get_check(long ikey, long iexpected) {
        quick_istr key(ikey), expected(iexpected);
        get_check(key.string(), expected.string());
    }
    void get_check_key8(long ikey, long iexpected) {
        quick_istr key(ikey, 8), expected(iexpected);
        get_check(key.string(), expected.string());
    }
    void get_check_key10(long ikey, long iexpected) {
        quick_istr key(ikey, 10), expected(iexpected);
        get_check(key.string(), expected.string());
    }
    void get_col_check(const Str &key, int col, const Str &expected);
    void get_col_check_key10(long ikey, int col, long iexpected) {
        quick_istr key(ikey, 10), expected(iexpected);
        get_col_check(key.string(), col, expected.string());
    }
    bool get_sync(long ikey);

    void put(const Str &key, const Str &value);
    void put(const char *key, const char *val) {
        put(Str(key, strlen(key)), Str(val, strlen(val)));
    }
    void put(long ikey, long ivalue) {
        quick_istr key(ikey), value(ivalue);
        put(key.string(), value.string());
    }
    void put_key8(long ikey, long ivalue) {
        quick_istr key(ikey, 8), value(ivalue);
        put(key.string(), value.string());
    }
    void put_key10(long ikey, long ivalue) {
        quick_istr key(ikey, 10), value(ivalue);
        put(key.string(), value.string());
    }
    void put_col(const Str &key, int col, const Str &value);
    void put_col_key10(long ikey, int col, long ivalue) {
        quick_istr key(ikey, 10), value(ivalue);
        put_col(key.string(), col, value.string());
    }

    bool remove_sync(long ikey);

    void puts_done() {
    }
    void wait_all() {
    }
    void rcu_quiesce() {
    }
    String make_message(StringAccum &sa) const;
    void notice(const char *fmt, ...);
    void fail(const char *fmt, ...);
    const Json& report(const Json& x) {
        return report_.merge(x);
    }
    void finish() {
        fprintf(stderr, "%d: %s\n", ti_->index(), report_.unparse().c_str());
    }
    threadinfo *ti_;
    query<row_type> q_[10];
    const char *testname_;
    kvrandom_lcg_nr rand;
    int checks_;
    Json report_;
    struct kvout *kvo_;
    static volatile int failing;
};

volatile int kvtest_client::failing;

void kvtest_client::get(long ikey, Str *value)
{
    quick_istr key(ikey);
    if (!q_[0].run_get1(tree->table(), key.string(), 0, *value, *ti_))
        *value = Str();
}

void kvtest_client::get(const Str &key)
{
    Str val;
    (void) q_[0].run_get1(tree->table(), key, 0, val, *ti_);
}

void kvtest_client::get_check(const Str &key, const Str &expected)
{
    Str val;
    if (!q_[0].run_get1(tree->table(), key, 0, val, *ti_)) {
        fail("get(%.*s) failed (expected %.*s)\n", key.len, key.s, expected.len, expected.s);
        return;
    }
    if (val.len != expected.len || memcmp(val.s, expected.s, val.len) != 0)
        fail("get(%.*s) returned unexpected value %.*s (expected %.*s)\n", key.len, key.s,
             std::min(val.len, 40), val.s, std::min(expected.len, 40), expected.s);
    else
        ++checks_;
}

void kvtest_client::get_col_check(const Str &key, int col, const Str &expected)
{
    Str val;
    if (!q_[0].run_get1(tree->table(), key, col, val, *ti_)) {
        fail("get.%d(%.*s) failed (expected %.*s)\n", col, key.len, key.s,
             expected.len, expected.s);
        return;
    }
    if (val.len != expected.len || memcmp(val.s, expected.s, val.len) != 0)
        fail("get.%d(%.*s) returned unexpected value %.*s (expected %.*s)\n",
             col, key.len, key.s, std::min(val.len, 40), val.s,
             std::min(expected.len, 40), expected.s);
    else
        ++checks_;
}

bool kvtest_client::get_sync(long ikey) {
    quick_istr key(ikey);
    Str val;
    return q_[0].run_get1(tree->table(), key.string(), 0, val, *ti_);
}

void kvtest_client::put(const Str &key, const Str &value) {
    while (failing)
        /* do nothing */;
    q_[0].run_replace(tree->table(), key, value, *ti_);
}

void kvtest_client::put_col(const Str &key, int col, const Str &value) {
    while (failing)
        /* do nothing */;
#if !MASSTREE_ROW_TYPE_STR
    if (!kvo_)
        kvo_ = new_kvout(-1, 2048);
    Json req[2] = {Json(col), Json(String::make_stable(value))};
    (void) q_[0].run_put(tree->table(), key, &req[0], &req[2], *ti_);
#else
    (void) key, (void) col, (void) value;
    assert(0);
#endif
}

bool kvtest_client::remove_sync(long ikey) {
    quick_istr key(ikey);
    bool removed = q_[0].run_remove(tree->table(), key.string(), *ti_);
    return removed;
}

String kvtest_client::make_message(StringAccum &sa) const {
    const char *begin = sa.begin();
    while (begin != sa.end() && isspace((unsigned char) *begin))
        ++begin;
    String s = String(begin, sa.end());
    if (!s.empty() && s.back() != '\n')
        s += '\n';
    return s;
}

void kvtest_client::notice(const char *fmt, ...) {
    va_list val;
    va_start(val, fmt);
    String m = make_message(StringAccum().vsnprintf(500, fmt, val));
    va_end(val);
    if (m)
        fprintf(stderr, "%d: %s", ti_->index(), m.c_str());
}

void kvtest_client::fail(const char *fmt, ...) {
    static nodeversion32 failing_lock(false);
    static nodeversion32 fail_message_lock(false);
    static String fail_message;
    failing = 1;

    va_list val;
    va_start(val, fmt);
    String m = make_message(StringAccum().vsnprintf(500, fmt, val));
    va_end(val);
    if (!m)
        m = "unknown failure";

    fail_message_lock.lock();
    if (fail_message != m) {
        fail_message = m;
        fprintf(stderr, "%d: %s", ti_->index(), m.c_str());
    }
    fail_message_lock.unlock();

    if (doprint) {
        failing_lock.lock();
        fprintf(stdout, "%d: %s", ti_->index(), m.c_str());
        tree->print(stdout);
        fflush(stdout);
    }

    always_assert(0);
}

static const char alphanum[] =
    "0123456789"
    "ABCDEFGHIJKLMNOPQRSTUVWXYZ"
    "abcdefghijklmnopqrstuvwxyz";

std::string gen_random(int len) {
    std::string tmp_s;
    tmp_s.reserve(len);

    for (int i = 0; i < len; ++i) {
        tmp_s += alphanum[rand() % (sizeof(alphanum) - 1)];
    }
    
    return tmp_s;
}

int main() {
    threadinfo *main_ti = threadinfo::make(threadinfo::TI_MAIN, -1);
    main_ti->pthread() = pthread_self();

    tree = new Masstree::default_table;
    tree->initialize(*main_ti);

    kvtest_client client("mtbasic");
    client.set_thread(main_ti);

    const int dataset_size = 1000000;
    const int len = 100;
    std::vector<std::string> dataset(dataset_size);

    printf("making dataset...\n");

    for (int i = 0; i < dataset_size; i++) {
        auto s = gen_random(len);
        dataset[i] = s;
    }

    printf("making masstree...\n");

    for (const std::string& str : dataset) {
        Str lcdfstr = Str(str);
        client.put(lcdfstr, lcdfstr);
    }

    const int nlookups = 1000000;
    std::vector<Str> lookups(nlookups);
    for (int i = 0; i < nlookups; i++) {
        lookups[i] = dataset[rand() % dataset.size()];
    }

    std::chrono::steady_clock::time_point tstart = std::chrono::steady_clock::now();

    for (Str& lookup : lookups) {
        client.get_check(lookup, lookup);
    }

    std::chrono::steady_clock::time_point tend = std::chrono::steady_clock::now();
    auto elapsed = std::chrono::duration_cast<std::chrono::microseconds>(tend - tstart).count();
    printf("lookup time: %ld us, %g lookups/us\n", elapsed, (double) nlookups / (double) elapsed);
}

