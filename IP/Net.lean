/-
  IP.Net — HFT-leaning TCP/IP stack (10 GbE XGMII ↔ TCP payload stream).

  Layering (each layer also lives as a sub-module under IP/Net/):
    CRC32     — Ethernet FCS, reflected CRC-32/IEEE-802.3
    Ethernet  — byte-feed RX framer (DMAC/SMAC/EthType parse +
                payload stream).  Wide-bus + FCS check are
                follow-up MVPs.
    ARP       — TBD: static table + request/reply
    IPv4      — TBD: header parse/emit + one's-complement checksum
    UDP       — TBD
    TCP       — TBD: server (passive open) + client (active open)
    HFTStack  — TBD: top-level wiring MAC ↔ TCP

  See task #341.
-/
import IP.Net.CRC32
import IP.Net.Ethernet
