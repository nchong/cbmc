/*******************************************************************\

Module:

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#include "java_bytecode_parse_tree.h"

#include <algorithm>
#include <ostream>

#include <util/symbol_table.h>
#include <util/namespace.h>

#include <langapi/language_util.h>

#include "expr2java.h"

void java_bytecode_parse_treet::output(std::ostream &out) const
{
  parsed_class.output(out);

  out << "Class references:\n";
  for(class_refst::const_iterator it=class_refs.begin();
      it!=class_refs.end();
      it++)
    out << "  " << *it << '\n';
}

void java_bytecode_parse_treet::classt::output(std::ostream &out) const
{
  for(const auto &annotation : annotations)
  {
    annotation.output(out);
    out << '\n';
  }

  out << "class " << name;
  if(!super_class.empty())
    out << " extends " << super_class;
  out << " {" << '\n';

  for(fieldst::const_iterator
      it=fields.begin();
      it!=fields.end();
      it++)
  {
    it->output(out);
  }

  out << '\n';

  for(methodst::const_iterator
      it=methods.begin();
      it!=methods.end();
      it++)
  {
    it->output(out);
  }

  out << '}' << '\n';
  out << '\n';
}

void java_bytecode_parse_treet::annotationt::output(std::ostream &out) const
{
  symbol_tablet symbol_table;
  namespacet ns(symbol_table);

  out << '@' << type2java(type, ns);

  if(!element_value_pairs.empty())
  {
    out << '(';

    bool first=true;
    for(const auto &element_value_pair : element_value_pairs)
    {
      if(first)
        first=false;
      else
        out << ", ";
      element_value_pair.output(out);
    }

    out << ')';
  }
}

void java_bytecode_parse_treet::annotationt::element_value_pairt::output(
  std::ostream &out) const
{
  symbol_tablet symbol_table;
  namespacet ns(symbol_table);

  out << '"' << element_name << '"' << '=';
  out << expr2java(value, ns);
}

/// Find an annotation given its name
/// \param annotations: A vector of annotationt
/// \param annotation_type_name: An irep_idt representing the name of the
///   annotation class, e.g. java::java.lang.SuppressWarnings
/// \return The first annotation with the given name in annotations if one
///    exists, an empty optionalt otherwise.
optionalt<java_bytecode_parse_treet::annotationt>
java_bytecode_parse_treet::find_annotation(
  const annotationst &annotations,
  const irep_idt &annotation_type_name)
{
  const auto annotation_it = std::find_if(
    annotations.begin(),
    annotations.end(),
    [&annotation_type_name](const annotationt &annotation) {
      if(annotation.type.id() != ID_pointer)
        return false;
      const typet &type = annotation.type.subtype();
      return type.id() == ID_symbol_type &&
             to_symbol_type(type).get_identifier() == annotation_type_name;
    });
  if(annotation_it == annotations.end())
    return {};
  return *annotation_it;
}

void java_bytecode_parse_treet::methodt::output(std::ostream &out) const
{
  symbol_tablet symbol_table;
  namespacet ns(symbol_table);

  for(const auto &annotation : annotations)
  {
    out << "  ";
    annotation.output(out);
    out << '\n';
  }

  out << "  ";

  if(is_public)
    out << "public ";

  if(is_protected)
    out << "protected ";

  if(is_private)
    out << "private ";

  if(is_static)
    out << "static ";

  if(is_final)
    out << "final ";

  if(is_native)
    out << "native ";

  if(is_synchronized)
    out << "synchronized ";

  out << name;
  out << " : " << descriptor;

  out << '\n';

  out << "  {" << '\n';

  for(const auto &i : instructions)
  {
    if(!i.source_location.get_line().empty())
      out << "    // " << i.source_location << '\n';

    out << "    " << i.address << ": ";
    out << i.statement;

    for(std::vector<exprt>::const_iterator
        a_it=i.args.begin(); a_it!=i.args.end(); a_it++)
    {
      if(a_it!=i.args.begin())
        out << ',';
      #if 0
      out << ' ' << from_expr(*a_it);
      #else
      out << ' ' << expr2java(*a_it, ns);
      #endif
    }

    out << '\n';
  }

  out << "  }" << '\n';

  out << '\n';

  out << "  Locals:\n";
  for(const auto &v : local_variable_table)
  {
    out << "    " << v.index << ": " << v.name << ' '
        << v.descriptor << '\n';
  }

  out << '\n';
}

void java_bytecode_parse_treet::fieldt::output(std::ostream &out) const
{
  for(const auto &annotation : annotations)
  {
    out << "  ";
    annotation.output(out);
    out << '\n';
  }

  out << "  ";

  if(is_public)
    out << "public ";

  if(is_static)
    out << "static ";

  out << name;
  out << " : " << descriptor << ';';

  out << '\n';
}
