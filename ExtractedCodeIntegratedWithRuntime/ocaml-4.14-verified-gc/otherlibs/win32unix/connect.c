/**************************************************************************/
/*                                                                        */
/*                                 OCaml                                  */
/*                                                                        */
/*   Xavier Leroy and Pascal Cuoq, projet Cristal, INRIA Rocquencourt     */
/*                                                                        */
/*   Copyright 1996 Institut National de Recherche en Informatique et     */
/*     en Automatique.                                                    */
/*                                                                        */
/*   All rights reserved.  This file is distributed under the terms of    */
/*   the GNU Lesser General Public License version 2.1, with the          */
/*   special exception on linking described in the file LICENSE.          */
/*                                                                        */
/**************************************************************************/

#include <caml/mlvalues.h>
#include <caml/signals.h>
#include "unixsupport.h"
#include "socketaddr.h"

CAMLprim value unix_connect(value socket, value address)
{
  SOCKET s = Socket_val(socket);
  union sock_addr_union addr;
  socklen_param_type addr_len;
  DWORD err = 0;

  get_sockaddr(address, &addr, &addr_len);
  caml_enter_blocking_section();
  if (connect(s, &addr.s_gen, addr_len) == -1)
    err = WSAGetLastError();
  caml_leave_blocking_section();
  if (err) {
    win32_maperr(err);
    uerror("connect", Nothing);
  }
  return Val_unit;
}
