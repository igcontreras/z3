/*++
Copyright (c) 2020 Microsoft Corporation

Module Name:

    euf_justification.h

Abstract:

    justification structure for euf

Author:

    Nikolaj Bjorner (nbjorner) 2020-08-23

Notes:

- congruence closure justifications are given a timestamp so it is easy to sort them.
  See the longer descriptoin in euf_proof_checker.cpp

--*/

#pragma once

namespace euf {

    class justification {
        enum class kind_t {
            axiom_t, 
            congruence_t, 
            external_t
        };
        kind_t m_kind;
        bool   m_comm;
        union {
            void*    m_external;
            uint64_t m_timestamp;
        };
        // -- general purpose mark
        unsigned m_mark : 1;

        justification(bool comm, uint64_t ts):
            m_kind(kind_t::congruence_t),
            m_comm(comm),
            m_timestamp(ts)
        {}

        justification(bool comm, uint64_t ts, bool mark)
        : m_kind(kind_t::congruence_t), m_comm(comm), m_timestamp(ts), m_mark(mark){}

        justification(void* ext):
            m_kind(kind_t::external_t),
            m_comm(false),
            m_external(ext)
        {}
        justification(void *ext, bool mark)
            : m_kind(kind_t::external_t), m_comm(false), m_external(ext),
              m_mark(mark) {}

      public:
        justification()
            : m_kind(kind_t::axiom_t), m_comm(false), m_external(nullptr) {
          m_mark = 0;
        }
      justification(bool mark)
          : m_kind(kind_t::axiom_t), m_comm(false), m_external(nullptr),
            m_mark(mark) {}

      static justification axiom() { return justification(); }
      static justification axiom(bool mark) { return justification(mark); }
      static justification congruence(bool c, uint64_t ts) {
        return justification(c, ts);
      }
      static justification congruence(bool c, uint64_t ts, bool mark) {
        return justification(c, ts, mark);
      }
      static justification external(void *ext) { return justification(ext); }
      static justification external(void *ext, bool mark) { return justification(ext, mark); }

      bool is_external() const { return m_kind == kind_t::external_t; }
      bool is_congruence() const { return m_kind == kind_t::congruence_t; }
      bool is_commutative() const { return m_comm; }
      uint64_t timestamp() const {
        SASSERT(is_congruence());
        return m_timestamp; }
        template <typename T>
        T*  ext() const { SASSERT(is_external()); return static_cast<T*>(m_external); }
        void set_mark(bool mark) { m_mark = mark; }
        justification & mark() { m_mark = true;
          return *this;
        }
        bool is_marked() { return m_mark; }

        justification copy(std::function<void*(void*)>& copy_justification) const {
            switch (m_kind) {
            case kind_t::external_t:
              return external(copy_justification(m_external),m_mark);
            case kind_t::axiom_t:
              return axiom(m_mark);
            case kind_t::congruence_t:
              return congruence(m_comm, m_timestamp, m_mark);
            default:
                UNREACHABLE();
                return axiom(m_mark);
            }
        }

        std::ostream& display(std::ostream& out, std::function<void (std::ostream&, void*)> const& ext) const {
            switch (m_kind) {
            case kind_t::external_t:
                if (ext)
                    ext(out, m_external);
                else
                    out << "external";
                return out;
            case kind_t::axiom_t:
                return out << "axiom";
            case kind_t::congruence_t:
                return out << "congruence";
            default:
                UNREACHABLE();
                return out;
            }
            return out;
        }
    };

    inline std::ostream& operator<<(std::ostream& out, justification const& j) {
        return j.display(out, nullptr);
    }
}
