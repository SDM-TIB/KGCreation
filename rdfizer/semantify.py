import os
import re
import csv
import sys
import uuid
import rdflib
import urllib
import getopt
import subprocess
from rdflib.plugins.sparql import prepareQuery
from configparser import ConfigParser, ExtendedInterpolation
from rdfizer.triples_map import TriplesMap as tm
import traceback
from mysql import connector
from concurrent.futures import ThreadPoolExecutor
import time
import json
import xml.etree.ElementTree as ET
import psycopg2
import types
from .functions import *
import pandas as pd
import tracemalloc

try:
	from triples_map import TriplesMap as tm
except:
	from .triples_map import TriplesMap as tm	

# Work in the rr:sqlQuery (change mapping parser query, add sqlite3 support, etc)
# Work in the "when subject is empty" thing (uuid.uuid4(), dependency graph over the ) 

global g_triples 
g_triples = {}
global number_triple
number_triple = 0
global triples
triples = []
global duplicate
duplicate = ""
global start_time
start_time = 0
global user, password, port, host
user, password, port, host = "", "", "", ""
global join_table 
join_table = {}
global po_table
po_table = {}
global enrichment
enrichment = ""
global id_number
id_number = 0
global dic_table
dic_table = {}
global general_predicates
general_predicates = {"http://www.w3.org/2000/01/rdf-schema#subClassOf":"",
						"http://www.w3.org/2002/07/owl#sameAs":"",
						"http://www.w3.org/2000/01/rdf-schema#seeAlso":"",
						"http://www.w3.org/2000/01/rdf-schema#subPropertyOf":""}

def dictionary_table_update(resource):
	if resource not in dic_table:
		global id_number
		dic_table[resource] = base36encode(id_number)
		id_number += 1

def hash_update(parent_data, parent_subject, child_object,join_id):
	hash_table = {}
	for row in parent_data:
		if child_object.parent[0] in row.keys():
			if row[child_object.parent[0]] in hash_table:
				if duplicate == "yes":
					if parent_subject.subject_map.subject_mapping_type == "reference":
						value = string_substitution(parent_subject.subject_map.value, ".+", row, "object")
						if value is not None:
							if "http" in value and "<" not in value:
								value = "<" + value[1:-1] + ">"
							elif "http" in value and "<" in value:
								value = value[1:-1] 
						if value not in hash_table[row[child_object.parent[0]]]:
							hash_table[row[child_object.parent[0]]].update({value : ""})
					else:
						value = string_substitution(parent_subject.subject_map.value, "{(.+?)}", row, "object")
						if value is not None:
							if "<" + value + ">" not in hash_table[row[child_object.parent[0]]]:
								hash_table[row[child_object.parent[0]]].update({"<" + value + ">" : ""}) 
				else:
					if parent_subject.subject_map.subject_mapping_type == "reference":
						value = string_substitution(parent_subject.subject_map.value, ".+", row, "object")
						if "http" in value and "<" not in value:
							value = "<" + value[1:-1] + ">"
						elif "http" in value and "<" in value:
							value = value[1:-1] 
						hash_table[row[child_object.parent[0]]].update({value : ""})
					else:
						value = string_substitution(parent_subject.subject_map.value, "{(.+?)}", row, "object")
						if value is not None:
							hash_table[row[child_object.parent[0]]].update({"<" + value + ">" : ""})

			else:
				if parent_subject.subject_map.subject_mapping_type == "reference":
					value = string_substitution(parent_subject.subject_map.value, ".+", row, "object")
					if value is not None:
						if "http" in value and "<" not in value:
							value = "<" + value[1:-1] + ">"
						elif "http" in value and "<" in value:
							value = value[1:-1] 
					hash_table.update({row[child_object.parent[0]] : [value]}) 
				else:
					value = string_substitution(parent_subject.subject_map.value, "{(.+?)}", row, "object")
					if value is not None:	
						hash_table.update({row[child_object.parent[0]] : {"<" + value + ">" : ""}})
	join_table[join_id].update(hash_table)

def hash_maker(parent_data, parent_subject, child_object):
	hash_table = {}
	for row in parent_data:
		if child_object.parent[0] in row.keys():
			if row[child_object.parent[0]] in hash_table:
				if duplicate == "yes":
					if parent_subject.subject_map.subject_mapping_type == "reference":
						value = string_substitution(parent_subject.subject_map.value, ".+", row, "object")
						if value is not None:
							if "http" in value and "<" not in value:
								value = "<" + value[1:-1] + ">"
							elif "http" in value and "<" in value:
								value = value[1:-1] 
						if value not in hash_table[row[child_object.parent[0]]]:
							hash_table[row[child_object.parent[0]]].update({value : ""})
					else:
						value = string_substitution(parent_subject.subject_map.value, "{(.+?)}", row, "object")
						if value is not None:
							if "<" + value + ">" not in hash_table[row[child_object.parent[0]]]:
								hash_table[row[child_object.parent[0]]].update({"<" + value + ">" : ""}) 
				else:
					if parent_subject.subject_map.subject_mapping_type == "reference":
						value = string_substitution(parent_subject.subject_map.value, ".+", row, "object")
						if "http" in value and "<" not in value:
							value = "<" + value[1:-1] + ">"
						elif "http" in value and "<" in value:
							value = value[1:-1] 
						hash_table[row[child_object.parent[0]]].update({value : ""})
					else:
						value = string_substitution(parent_subject.subject_map.value, "{(.+?)}", row, "object")
						if value is not None:
							hash_table[row[child_object.parent[0]]].update({"<" + value + ">" : ""})

			else:
				if parent_subject.subject_map.subject_mapping_type == "reference":
					value = string_substitution(parent_subject.subject_map.value, ".+", row, "object")
					if value is not None:
						if "http" in value and "<" not in value:
							value = "<" + value[1:-1] + ">"
						elif "http" in value and "<" in value:
							value = value[1:-1] 
					hash_table.update({row[child_object.parent[0]] : {value : ""}}) 
				else:
					value = string_substitution(parent_subject.subject_map.value, "{(.+?)}", row, "object")
					if value is not None:	
						hash_table.update({row[child_object.parent[0]] : {"<" + value + ">" : ""}})
	join_table.update({parent_subject.triples_map_id + "_" + child_object.child[0] : hash_table})

def hash_maker_list(parent_data, parent_subject, child_object):
	hash_table = {}
	for row in parent_data:
		if sublist(child_object.parent,row.keys()):
			if child_list_value(child_object.parent,row) in hash_table:
				if duplicate == "yes":
					if parent_subject.subject_map.subject_mapping_type == "reference":
						value = string_substitution(parent_subject.subject_map.value, ".+", row, "object")
						if value is not None:
							if "http" in value and "<" not in value:
								value = "<" + value[1:-1] + ">"
							elif "http" in value and "<" in value:
								value = value[1:-1] 
						if value not in hash_table[child_list_value(child_object.parent,row)]:
							hash_table[child_list_value(child_object.parent,row)].update({value : ""})
					else:
						value = string_substitution(parent_subject.subject_map.value, "{(.+?)}", row, "object")
						if value is not None:
							if "<" + value + ">" not in hash_table[child_list_value(child_object.parent,row)]:
								hash_table[child_list_value(child_object.parent,row)].update({"<" + value + ">" : ""}) 
				else:
					if parent_subject.subject_map.subject_mapping_type == "reference":
						value = string_substitution(parent_subject.subject_map.value, ".+", row, "object")
						if "http" in value and "<" not in value:
							value = "<" + value[1:-1] + ">"
						elif "http" in value and "<" in value:
							value = value[1:-1] 
						hash_table[child_list_value(child_object.parent,row)].update({value : "object"})
					else:
						value = string_substitution(parent_subject.subject_map.value, "{(.+?)}", row, "object")
						if value is not None:
							hash_table[child_list_value(child_object.parent,row)].update({"<" + value + ">" : ""})

			else:
				if parent_subject.subject_map.subject_mapping_type == "reference":
					value = string_substitution(parent_subject.subject_map.value, ".+", row, "object")
					if value is not None:
						if "http" in value and "<" not in value:
							value = "<" + value[1:-1] + ">"
						elif "http" in value and "<" in value:
							value = value[1:-1] 
					hash_table.update({child_list_value(child_object.parent,row) : {value : "object"}}) 
				else:
					value = string_substitution(parent_subject.subject_map.value, "{(.+?)}", row, "object") 
					if value is not None:	
						hash_table.update({child_list_value(child_object.parent,row) : {"<" + value + ">" : ""}})
	join_table.update({parent_subject.triples_map_id + "_" + child_list(child_object.child) : hash_table})


def hash_maker_array(parent_data, parent_subject, child_object):
	hash_table = {}
	row_headers=[x[0] for x in parent_data.description]
	for row in parent_data:
		element =row[row_headers.index(child_object.parent[0])]
		if type(element) is int:
			element = str(element)
		if row[row_headers.index(child_object.parent[0])] in hash_table:
			if duplicate == "yes":
				if "<" + string_substitution_array(parent_subject.subject_map.value, "{(.+?)}", row, row_headers,"object") + ">" not in hash_table[row[row_headers.index(child_object.parent[0])]]:
					hash_table[element].update({"<" + string_substitution_array(parent_subject.subject_map.value, "{(.+?)}", row, row_headers,"object") + ">" : ""})
			else:
				hash_table[element].update({"<" + string_substitution_array(parent_subject.subject_map.value, "{(.+?)}", row, row_headers, "object") + ">" : ""})
			
		else:
			hash_table.update({element : {"<" + string_substitution_array(parent_subject.subject_map.value, "{(.+?)}", row, row_headers, "object") + ">" : ""}}) 
	join_table.update({parent_subject.triples_map_id + "_" + child_object.child[0]  : hash_table})

def hash_maker_array_list(parent_data, parent_subject, child_object, r_w):
	hash_table = {}
	row_headers=[x[0] for x in parent_data.description]
	for row in parent_data:
		if child_list_value_array(child_object.parent,row,row_headers) in hash_table:
			if duplicate == "yes":
				if parent_subject.subject_map.subject_mapping_type == "reference":
					value = string_substitution_array(parent_subject.subject_map.value, ".+", row, row_headers,"object")
					if value is not None:
						if "http" in value and "<" not in value:
							value = "<" + value[1:-1] + ">"
						elif "http" in value and "<" in value:
							value = value[1:-1] 
					if value not in hash_table[child_list_value_array(child_object.parent,row,row_headers)]:
						hash_table[child_list_value_array(child_object.parent,row,row_headers)].update({value + ">" : "object"})

				else:
					if "<" + string_substitution_array(parent_subject.subject_map.value, "{(.+?)}", row, row_headers,"object") + ">" not in hash_table[child_list_value_array(child_object.parent,row,row_headers)]:
						hash_table[child_list_value_array(child_object.parent,row,row_headers)].update({"<" + string_substitution_array(parent_subject.subject_map.value, "{(.+?)}", row, row_headers,"object") + ">" : "object"})
			else:
				if parent_subject.subject_map.subject_mapping_type == "reference":
					value = string_substitution_array(parent_subject.subject_map.value, ".+", row, row_headers,"object")
					if value is not None:
						if "http" in value and "<" not in value:
							value = "<" + value[1:-1] + ">"
						elif "http" in value and "<" in value:
							value = value[1:-1] 
					hash_table[child_list_value_array(child_object.parent,row,row_headers)].update({value : "object"})
				else:
					hash_table[child_list_value_array(child_object.parent,row,row_headers)].update({"<" + string_substitution_array(parent_subject.subject_map.value, "{(.+?)}", row, row_headers, "object") + ">" : "object"})
			
		else:
			if parent_subject.subject_map.subject_mapping_type == "reference":
				value = string_substitution_array(parent_subject.subject_map.value, ".+", row, row_headers,"object")
				if value is not None:
					if "http" in value and "<" not in value:
						value = "<" + value[1:-1] + ">"
					elif "http" in value and "<" in value:
							value = value[1:-1]
				hash_table.update({child_list_value_array(child_object.parent,row,row_headers):{value : "object"}})
			else:
				hash_table.update({child_list_value_array(child_object.parent,row,row_headers) : {"<" + string_substitution_array(parent_subject.subject_map.value, "{(.+?)}", row, row_headers, "object") + ">" : "object"}}) 
	join_table.update({parent_subject.triples_map_id + "_" + child_list(child_object.child)  : hash_table})

def mapping_parser(mapping_file):

	"""
	(Private function, not accessible from outside this package)

	Takes a mapping file in Turtle (.ttl) or Notation3 (.n3) format and parses it into a list of
	TriplesMap objects (refer to TriplesMap.py file)

	Parameters
	----------
	mapping_file : string
		Path to the mapping file

	Returns
	-------
	A list of TriplesMap objects containing all the parsed rules from the original mapping file
	"""

	mapping_graph = rdflib.Graph()

	try:
		mapping_graph.load(mapping_file, format='n3')
	except Exception as n3_mapping_parse_exception:
		print(n3_mapping_parse_exception)
		print('Could not parse {} as a mapping file'.format(mapping_file))
		print('Aborting...')
		sys.exit(1)

	mapping_query = """
		prefix rr: <http://www.w3.org/ns/r2rml#> 
		prefix rml: <http://semweb.mmlab.be/ns/rml#> 
		prefix ql: <http://semweb.mmlab.be/ns/ql#> 
		prefix d2rq: <http://www.wiwiss.fu-berlin.de/suhl/bizer/D2RQ/0.1#> 
		SELECT DISTINCT *
		WHERE {

	# Subject -------------------------------------------------------------------------
			?triples_map_id rml:logicalSource ?_source .
			OPTIONAL{?_source rml:source ?data_source .}
			OPTIONAL {?_source rml:referenceFormulation ?ref_form .}
			OPTIONAL { ?_source rml:iterator ?iterator . }
			OPTIONAL { ?_source rr:tableName ?tablename .}
			OPTIONAL { ?_source rml:query ?query .}

			?triples_map_id rr:subjectMap ?_subject_map .
			OPTIONAL {?_subject_map rr:template ?subject_template .}
			OPTIONAL {?_subject_map rml:reference ?subject_reference .}
			OPTIONAL {?_subject_map rr:constant ?subject_constant}
			OPTIONAL { ?_subject_map rr:class ?rdf_class . }
			OPTIONAL { ?_subject_map rr:termType ?termtype . }
			OPTIONAL { ?_subject_map rr:graph ?graph . }
			OPTIONAL { ?_subject_map rr:graphMap ?_graph_structure .
					   ?_graph_structure rr:constant ?graph . }
			OPTIONAL { ?_subject_map rr:graphMap ?_graph_structure .
					   ?_graph_structure rr:template ?graph . }		   

	# Predicate -----------------------------------------------------------------------
			OPTIONAL {
			?triples_map_id rr:predicateObjectMap ?_predicate_object_map .
			
			OPTIONAL {
				?triples_map_id rr:predicateObjectMap ?_predicate_object_map .
				?_predicate_object_map rr:predicateMap ?_predicate_map .
				?_predicate_map rr:constant ?predicate_constant .
			}
			OPTIONAL {
				?_predicate_object_map rr:predicateMap ?_predicate_map .
				?_predicate_map rr:template ?predicate_template .
			}
			OPTIONAL {
				?_predicate_object_map rr:predicateMap ?_predicate_map .
				?_predicate_map rml:reference ?predicate_reference .
			}
			OPTIONAL {
				?_predicate_object_map rr:predicate ?predicate_constant_shortcut .
			 }
			

	# Object --------------------------------------------------------------------------
			OPTIONAL {
				?_predicate_object_map rr:objectMap ?_object_map .
				?_object_map rr:constant ?object_constant .
				OPTIONAL {
					?_object_map rr:datatype ?object_datatype .
				}
			}
			OPTIONAL {
				?_predicate_object_map rr:objectMap ?_object_map .
				?_object_map rr:template ?object_template .
				OPTIONAL {?_object_map rr:termType ?term .}
				OPTIONAL {
					?_object_map rr:datatype ?object_datatype .
				}
			}
			OPTIONAL {
				?_predicate_object_map rr:objectMap ?_object_map .
				?_object_map rml:reference ?object_reference .
				OPTIONAL { ?_object_map rr:language ?language .}
				OPTIONAL {?_object_map rr:termType ?term .}
				OPTIONAL {
					?_object_map rr:datatype ?object_datatype .
				}
			}
			OPTIONAL {
				?_predicate_object_map rr:objectMap ?_object_map .
				?_object_map rr:parentTriplesMap ?object_parent_triples_map .
				OPTIONAL {
					?_object_map rr:joinCondition ?join_condition .
					?join_condition rr:child ?child_value;
								 rr:parent ?parent_value.
					OPTIONAL {?_object_map rr:termType ?term .}
				}
			}
			OPTIONAL {
				?_predicate_object_map rr:object ?object_constant_shortcut .
				OPTIONAL {
					?_object_map rr:datatype ?object_datatype .
				}
			}
			OPTIONAL {?_predicate_object_map rr:graph ?predicate_object_graph .}
			OPTIONAL { ?_predicate_object_map  rr:graphMap ?_graph_structure .
					   ?_graph_structure rr:constant ?predicate_object_graph  . }
			OPTIONAL { ?_predicate_object_map  rr:graphMap ?_graph_structure .
					   ?_graph_structure rr:template ?predicate_object_graph  . }	
			}
			OPTIONAL {
				?_source a d2rq:Database;
  				d2rq:jdbcDSN ?jdbcDSN; 
  				d2rq:jdbcDriver ?jdbcDriver; 
			    d2rq:username ?user;
			    d2rq:password ?password .
			}
		} """

	mapping_query_results = mapping_graph.query(mapping_query)
	triples_map_list = []


	for result_triples_map in mapping_query_results:
		triples_map_exists = False
		for triples_map in triples_map_list:
			triples_map_exists = triples_map_exists or (str(triples_map.triples_map_id) == str(result_triples_map.triples_map_id))
		
		if not triples_map_exists:
			if result_triples_map.subject_template is not None:
				if result_triples_map.rdf_class is None:
					reference, condition = string_separetion(str(result_triples_map.subject_template))
					subject_map = tm.SubjectMap(str(result_triples_map.subject_template), condition, "template", [result_triples_map.rdf_class], result_triples_map.termtype, [result_triples_map.graph])
				else:
					reference, condition = string_separetion(str(result_triples_map.subject_template))
					subject_map = tm.SubjectMap(str(result_triples_map.subject_template), condition, "template", [str(result_triples_map.rdf_class)], result_triples_map.termtype, [result_triples_map.graph])
			elif result_triples_map.subject_reference is not None:
				if result_triples_map.rdf_class is None:
					reference, condition = string_separetion(str(result_triples_map.subject_reference))
					subject_map = tm.SubjectMap(str(result_triples_map.subject_reference), condition, "reference", [result_triples_map.rdf_class], result_triples_map.termtype, [result_triples_map.graph])
				else:
					reference, condition = string_separetion(str(result_triples_map.subject_reference))
					subject_map = tm.SubjectMap(str(result_triples_map.subject_reference), condition, "reference", [str(result_triples_map.rdf_class)], result_triples_map.termtype, [result_triples_map.graph])
			elif result_triples_map.subject_constant is not None:
				if result_triples_map.rdf_class is None:
					reference, condition = string_separetion(str(result_triples_map.subject_constant))
					subject_map = tm.SubjectMap(str(result_triples_map.subject_constant), condition, "constant", [result_triples_map.rdf_class], result_triples_map.termtype, [result_triples_map.graph])
				else:
					reference, condition = string_separetion(str(result_triples_map.subject_constant))
					subject_map = tm.SubjectMap(str(result_triples_map.subject_constant), condition, "constant", [str(result_triples_map.rdf_class)], result_triples_map.termtype, [result_triples_map.graph])
				
			mapping_query_prepared = prepareQuery(mapping_query)


			mapping_query_prepared_results = mapping_graph.query(mapping_query_prepared, initBindings={'triples_map_id': result_triples_map.triples_map_id})

			join_predicate = {}
			predicate_object_maps_list = []
			predicate_object_graph = {}
			for result_predicate_object_map in mapping_query_prepared_results:
				join = True
				if result_predicate_object_map.predicate_constant is not None:
					predicate_map = tm.PredicateMap("constant", str(result_predicate_object_map.predicate_constant), "")
					predicate_object_graph[str(result_predicate_object_map.predicate_constant)] = result_triples_map.predicate_object_graph
				elif result_predicate_object_map.predicate_constant_shortcut is not None:
					predicate_map = tm.PredicateMap("constant shortcut", str(result_predicate_object_map.predicate_constant_shortcut), "")
					predicate_object_graph[str(result_predicate_object_map.predicate_constant_shortcut)] = result_triples_map.predicate_object_graph
				elif result_predicate_object_map.predicate_template is not None:
					template, condition = string_separetion(str(result_predicate_object_map.predicate_template))
					predicate_map = tm.PredicateMap("template", template, condition)
				elif result_predicate_object_map.predicate_reference is not None:
					reference, condition = string_separetion(str(result_predicate_object_map.predicate_reference))
					predicate_map = tm.PredicateMap("reference", reference, condition)
				else:
					predicate_map = tm.PredicateMap("None", "None", "None")

				if result_predicate_object_map.object_constant is not None:
					object_map = tm.ObjectMap("constant", str(result_predicate_object_map.object_constant), str(result_predicate_object_map.object_datatype), "None", "None", result_predicate_object_map.term, result_predicate_object_map.language)
				elif result_predicate_object_map.object_template is not None:
					object_map = tm.ObjectMap("template", str(result_predicate_object_map.object_template), str(result_predicate_object_map.object_datatype), "None", "None", result_predicate_object_map.term, result_predicate_object_map.language)
				elif result_predicate_object_map.object_reference is not None:
					object_map = tm.ObjectMap("reference", str(result_predicate_object_map.object_reference), str(result_predicate_object_map.object_datatype), "None", "None", result_predicate_object_map.term, result_predicate_object_map.language)
				elif result_predicate_object_map.object_parent_triples_map is not None:
					if predicate_map.value not in join_predicate:
						join_predicate[predicate_map.value] = {"predicate":predicate_map, "childs":[str(result_predicate_object_map.child_value)], "parents":[str(result_predicate_object_map.parent_value)], "triples_map":str(result_predicate_object_map.object_parent_triples_map)}
					else:
						join_predicate[predicate_map.value]["childs"].append(str(result_predicate_object_map.child_value))
						join_predicate[predicate_map.value]["parents"].append(str(result_predicate_object_map.parent_value))
					join = False
				elif result_predicate_object_map.object_constant_shortcut is not None:
					object_map = tm.ObjectMap("constant shortcut", str(result_predicate_object_map.object_constant_shortcut), str(result_predicate_object_map.object_datatype), "None", "None", result_predicate_object_map.term, result_predicate_object_map.language)
				else:
					object_map = tm.ObjectMap("None", "None", "None", "None", "None", "None", "None")
				if join:
					predicate_object_maps_list += [tm.PredicateObjectMap(predicate_map, object_map,predicate_object_graph)]
				join = True
			if join_predicate:
				for jp in join_predicate.keys():
					object_map = tm.ObjectMap("parent triples map", join_predicate[jp]["triples_map"], str(result_predicate_object_map.object_datatype), join_predicate[jp]["childs"], join_predicate[jp]["parents"],result_predicate_object_map.term, result_predicate_object_map.language)
					predicate_object_maps_list += [tm.PredicateObjectMap(join_predicate[jp]["predicate"], object_map,predicate_object_graph)]

			current_triples_map = tm.TriplesMap(str(result_triples_map.triples_map_id), str(result_triples_map.data_source), subject_map, predicate_object_maps_list, ref_form=str(result_triples_map.ref_form), iterator=str(result_triples_map.iterator), tablename=str(result_triples_map.tablename), query=str(result_triples_map.query))
			triples_map_list += [current_triples_map]

		else:
			for triples_map in triples_map_list:
				if str(triples_map.triples_map_id) == str(result_triples_map.triples_map_id):
					if result_triples_map.rdf_class not in triples_map.subject_map.rdf_class:
						triples_map.subject_map.rdf_class.append(result_triples_map.rdf_class)
					if result_triples_map.graph not in triples_map.subject_map.graph:
						triples_map.graph.append(result_triples_map.graph)


	return triples_map_list


def semantify_file(triples_map, triples_map_list, delimiter, output_file_descriptor, csv_file, dataset_name, data):
	
	print("\n\nTM:",triples_map.triples_map_name)

	"""
	(Private function, not accessible from outside this package)

	Takes a triples-map rule and applies it to each one of the rows of its CSV data
	source

	Parameters
	----------
	triples_map : TriplesMap object
		Mapping rule consisting of a logical source, a subject-map and several predicateObjectMaps
		(refer to the TriplesMap.py file in the triplesmap folder)
	triples_map_list : list of TriplesMap objects
		List of triples-maps parsed from current mapping being used for the semantification of a
		dataset (mainly used to perform rr:joinCondition mappings)
	delimiter : string
		Delimiter value for the CSV or TSV file ("\s" and "\t" respectively)
	output_file_descriptor : file object 
		Descriptor to the output file (refer to the Python 3 documentation)

	Returns
	-------
	An .nt file per each dataset mentioned in the configuration file semantified.
	If the duplicates are asked to be removed in main memory, also returns a -min.nt
	file with the triples sorted and with the duplicates removed.
	"""
	object_list = []
	
	i = 0
	for row in data:
		subject_value = string_substitution(triples_map.subject_map.value, "{(.+?)}", row, "subject") 	
		if triples_map.subject_map.subject_mapping_type == "template":
			if triples_map.subject_map.term_type is None:
				if triples_map.subject_map.condition == "":

					try:
						subject = "<" + subject_value + ">"
					except:
						subject = None

				else:
				#	field, condition = condition_separetor(triples_map.subject_map.condition)
				#	if row[field] == condition:
					try:
						subject = "<" + subject_value  + ">"
					except:
						subject = None
			else:
				if "IRI" in triples_map.subject_map.term_type:
					if triples_map.subject_map.condition == "":

						try:
							subject = "<http://example.com/base/" + subject_value + ">"
						except:
							subject = None

					else:
					#	field, condition = condition_separetor(triples_map.subject_map.condition)
					#	if row[field] == condition:
						try:
							subject = "<http://example.com/base/" + subject_value + ">"
						except:
							subject = None
					
				elif "BlankNode" in triples_map.subject_map.term_type:
					if triples_map.subject_map.condition == "":

						try:
							subject = "_:" + subject_value 
						except:
							subject = None

					else:
					#	field, condition = condition_separetor(triples_map.subject_map.condition)
					#	if row[field] == condition:
						try:
							subject = "_:" + subject_value  
						except:
							subject = None
				else:
					if triples_map.subject_map.condition == "":

						try:
							subject = "<" + subject_value + ">" 
						except:
							subject = None

					else:
					#	field, condition = condition_separetor(triples_map.subject_map.condition)
					#	if row[field] == condition:
						try:
							subject = "<" + subject_value + ">"
						except:
							subject = None

		elif "reference" in triples_map.subject_map.subject_mapping_type:
			if triples_map.subject_map.condition == "":
				subject_value = string_substitution(triples_map.subject_map.value, ".+", row, "subject")
				subject_value = subject_value[1:-1]
				try:
					if " " not in subject_value:
						subject = "<http://example.com/base/" + subject_value + ">"
					else:
						print("<http://example.com/base/" + subject_value + "> is an invalid URL")
						subject = None 
				except:
					subject = None

			else:
			#	field, condition = condition_separetor(triples_map.subject_map.condition)
			#	if row[field] == condition:
				try:
					subject = "<http://example.com/base/" + subject_value + ">"
				except:
					subject = None

		elif "constant" in triples_map.subject_map.subject_mapping_type:
			subject = "<" + subject_value + ">"

		else:
			if triples_map.subject_map.condition == "":

				try:
					subject =  "\"" + triples_map.subject_map.value + "\""
				except:
					subject = None

			else:
			#	field, condition = condition_separetor(triples_map.subject_map.condition)
			#	if row[field] == condition:
				try:
					subject =  "\"" + triples_map.subject_map.value + "\""
				except:
					subject = None

		if triples_map.subject_map.rdf_class is not None and subject is not None:
			predicate = "<http://www.w3.org/1999/02/22-rdf-syntax-ns#type>"
			for rdf_class in triples_map.subject_map.rdf_class:
				if rdf_class is not None:
					obj = "<{}>".format(rdf_class)
					dictionary_table_update(subject)
					dictionary_table_update(obj)
					dictionary_table_update(predicate + "_" + obj)
					rdf_type = subject + " " + predicate + " " + obj + ".\n"
					for graph in triples_map.subject_map.graph:
						if graph is not None and "defaultGraph" not in graph:
							if "{" in graph:	
								rdf_type = rdf_type[:-2] + " <" + string_substitution(graph, "{(.+?)}", row, "subject") + "> .\n"
								dictionary_table_update("<" + string_substitution(graph, "{(.+?)}", row, "subject") + ">")
							else:
								rdf_type = rdf_type[:-2] + " <" + graph + "> .\n"
								dictionary_table_update("<" + graph + ">")
					if duplicate == "yes":
						if dic_table[predicate + "_" + obj] not in g_triples:
							output_file_descriptor.write(rdf_type)
							if (number_triple + i + 1) % 10000 == 0:
								csv_file.writerow([dataset_name, number_triple + i + 1, time.time()-start_time])
							g_triples.update({dic_table[predicate  + "_" + obj ] : {dic_table[subject] + "_" + dic_table[obj]: ""}})
							i += 1
						elif dic_table[subject] + "_" + dic_table[obj] not in g_triples[dic_table[predicate + "_" + obj]]:
							output_file_descriptor.write(rdf_type)
							if (number_triple + i + 1) % 10000 == 0:
								csv_file.writerow([dataset_name, number_triple + i + 1, time.time()-start_time])
							g_triples[dic_table[predicate + "_" + obj]].update({dic_table[subject] + "_" + dic_table[obj] : ""})
							i += 1
					else:
						output_file_descriptor.write(rdf_type)
						if (number_triple + i + 1) % 10000 == 0:
							csv_file.writerow([dataset_name, number_triple + i + 1, time.time()-start_time])
						i += 1

		
		for predicate_object_map in triples_map.predicate_object_maps_list:
			if predicate_object_map.predicate_map.mapping_type == "constant" or predicate_object_map.predicate_map.mapping_type == "constant shortcut":
				predicate = "<" + predicate_object_map.predicate_map.value + ">"
			elif predicate_object_map.predicate_map.mapping_type == "template":
				if predicate_object_map.predicate_map.condition != "":
						#field, condition = condition_separetor(predicate_object_map.predicate_map.condition)
						#if row[field] == condition:
						try:
							predicate = "<" + string_substitution(predicate_object_map.predicate_map.value, "{(.+?)}", row, "predicate") + ">"
						except:
							predicate = None
						#else:
						#	predicate = None
				else:
					try:
						predicate = "<" + string_substitution(predicate_object_map.predicate_map.value, "{(.+?)}", row, "predicate") + ">"
					except:
						predicate = None
			elif predicate_object_map.predicate_map.mapping_type == "reference":
					if predicate_object_map.predicate_map.condition != "":
						#field, condition = condition_separetor(predicate_object_map.predicate_map.condition)
						#if row[field] == condition:
						predicate = string_substitution(predicate_object_map.predicate_map.value, ".+", row, "predicate")
						#else:
						#	predicate = None
					else:
						predicate = string_substitution(predicate_object_map.predicate_map.value, ".+", row, "predicate")
			else:
				predicate = None

			if predicate_object_map.object_map.mapping_type == "constant" or predicate_object_map.object_map.mapping_type == "constant shortcut":
				if "/" in predicate_object_map.object_map.value:
					object = "<" + predicate_object_map.object_map.value + ">"
				else:
					object = "\"" + predicate_object_map.object_map.value + "\""
			elif predicate_object_map.object_map.mapping_type == "template":
				try:
					if predicate_object_map.object_map.term is None:
						object = "<" + string_substitution(predicate_object_map.object_map.value, "{(.+?)}", row, "object") + ">"
					elif "IRI" in predicate_object_map.object_map.term:
						object = "<" + string_substitution(predicate_object_map.object_map.value, "{(.+?)}", row, "object") + ">"
					else:
						object = "\"" + string_substitution(predicate_object_map.object_map.value, "{(.+?)}", row, "object") + "\""
				except TypeError:
					object = None
			elif predicate_object_map.object_map.mapping_type == "reference":
				object = string_substitution(predicate_object_map.object_map.value, ".+", row, "object")
				if object is not None:
					if predicate_object_map.object_map.datatype is not None:
						object = "\"" + object[1:-1] + "\"" + "^^<{}>".format(predicate_object_map.object_map.datatype)
					elif predicate_object_map.object_map.language is not None:
						if "spanish" in predicate_object_map.object_map.language or "es" in predicate_object_map.object_map.language :
							object += "@es"
						elif "english" in predicate_object_map.object_map.language or "en" in predicate_object_map.object_map.language :
							object += "@en"
						elif "IRI" in predicate_object_map.object_map.term:
							if " " not in object:
								object = "<" + object + ">"
							else:
								object = None 
			elif predicate_object_map.object_map.mapping_type == "parent triples map":
				if subject is not None:
					for triples_map_element in triples_map_list:
						if triples_map_element.triples_map_id == predicate_object_map.object_map.value:
							if triples_map_element.data_source != triples_map.data_source:
								if len(predicate_object_map.object_map.child) == 1:
									if (triples_map_element.triples_map_id + "_" + predicate_object_map.object_map.child[0]) not in join_table:
										if str(triples_map_element.file_format).lower() == "csv" or triples_map_element.file_format == "JSONPath":
											with open(str(triples_map_element.data_source), "r") as input_file_descriptor:
												if str(triples_map_element.file_format).lower() == "csv":
													data = csv.DictReader(input_file_descriptor, delimiter=delimiter)
													hash_maker(data, triples_map_element, predicate_object_map.object_map)
												else:
													data = json.load(input_file_descriptor)
													if isinstance(data, list):
														hash_maker(data, triples_map_element, predicate_object_map.object_map)
													elif len(data) < 2:
														hash_maker(data[list(data.keys())[0]], triples_map_element, predicate_object_map.object_map)

										elif triples_map_element.file_format == "XPath":
											with open(str(triples_map_element.data_source), "r") as input_file_descriptor:
												child_tree = ET.parse(input_file_descriptor)
												child_root = child_tree.getroot()
												hash_maker_xml(child_root, triples_map_element, predicate_object_map.object_map)								
										else:
											database, query_list = translate_sql(triples_map)
											db = connector.connect(host=host, port=int(port), user=user, password=password)
											cursor = db.cursor(buffered=True)
											cursor.execute("use " + database)
											for query in query_list:
												cursor.execute(query)
											hash_maker_array(cursor, triples_map_element, predicate_object_map.object_map)

									if sublist(predicate_object_map.object_map.child,row.keys()):
										if child_list_value(predicate_object_map.object_map.child,row) in join_table[triples_map_element.triples_map_id + "_" + predicate_object_map.object_map.child[0]]:
											object_list = join_table[triples_map_element.triples_map_id + "_" + child_list(predicate_object_map.object_map.child)][child_list_value(predicate_object_map.object_map.child,row)]
										else:
											if str(triples_map_element.file_format).lower() == "csv" or triples_map_element.file_format == "JSONPath":
												with open(str(triples_map_element.data_source), "r") as input_file_descriptor:
													if str(triples_map_element.file_format).lower() == "csv":
														data = csv.DictReader(input_file_descriptor, delimiter=delimiter)
														hash_update(data, triples_map_element, predicate_object_map.object_map, triples_map_element.triples_map_id + "_" + predicate_object_map.object_map.child[0])
													else:
														data = json.load(input_file_descriptor)
														if isinstance(data, list):
															hash_update(data, triples_map_element, predicate_object_map.object_map, triples_map_element.triples_map_id + "_" + predicate_object_map.object_map.child[0])
														elif len(data) < 2:	
															hash_update(data[list(data.keys())[0]], triples_map_element, predicate_object_map.object_map, triples_map_element.triples_map_id + "_" + predicate_object_map.object_map.child[0])
											if child_list_value(predicate_object_map.object_map.child,row) in join_table[triples_map_element.triples_map_id + "_" + predicate_object_map.object_map.child[0]]:
												object_list = join_table[triples_map_element.triples_map_id + "_" + predicate_object_map.object_map.child[0]][row[predicate_object_map.object_map.child[0]]]
											else:
												object_list = []
									object = None
								else:
									if (triples_map_element.triples_map_id + "_" + child_list(predicate_object_map.object_map.child)) not in join_table:
										if str(triples_map_element.file_format).lower() == "csv" or triples_map_element.file_format == "JSONPath":
											with open(str(triples_map_element.data_source), "r") as input_file_descriptor:
												if str(triples_map_element.file_format).lower() == "csv":
													data = csv.DictReader(input_file_descriptor, delimiter=delimiter)
													hash_maker_list(data, triples_map_element, predicate_object_map.object_map)
												else:
													data = json.load(input_file_descriptor)
													if isinstance(data, list):
														hash_maker_list(data, triples_map_element, predicate_object_map.object_map)
													elif len(data) < 2:
														hash_maker_list(data[list(data.keys())[0]], triples_map_element, predicate_object_map.object_map)

										elif triples_map_element.file_format == "XPath":
											with open(str(triples_map_element.data_source), "r") as input_file_descriptor:
												child_tree = ET.parse(input_file_descriptor)
												child_root = child_tree.getroot()
												hash_maker_xml(child_root, triples_map_element, predicate_object_map.object_map)						
										else:
											database, query_list = translate_sql(triples_map)
											db = connector.connect(host=host, port=int(port), user=user, password=password)
											cursor = db.cursor(buffered=True)
											cursor.execute("use " + database)
											for query in query_list:
												cursor.execute(query)
											hash_maker_array(cursor, triples_map_element, predicate_object_map.object_map)
									if sublist(predicate_object_map.object_map.child,row.keys()):
										if child_list_value(predicate_object_map.object_map.child,row) in join_table[triples_map_element.triples_map_id + "_" + child_list(predicate_object_map.object_map.child)]:
											object_list = join_table[triples_map_element.triples_map_id + "_" + child_list(predicate_object_map.object_map.child)][child_list_value(predicate_object_map.object_map.child,row)]
										else:
											object_list = []
									object = None
							else:
								if predicate_object_map.object_map.parent is not None:
									if str(triples_map_element.triples_map_id) + "_" + str(predicate_object_map.object_map.child) not in join_table:
										with open(str(triples_map_element.data_source), "r") as input_file_descriptor:
											if str(triples_map_element.file_format).lower() == "csv":
												data = csv.DictReader(input_file_descriptor, delimiter=delimiter)
												hash_maker(data, triples_map_element, predicate_object_map.object_map)
											else:
												data = json.load(input_file_descriptor)
												if isinstance(data, list):
													hash_maker(data, triples_map_element, predicate_object_map.object_map)
												else:
													hash_maker(data[list(data.keys())[0]], triples_map_element, predicate_object_map.object_map)
									if sublist(predicate_object_map.object_map.child,row.keys()):
										if child_list_value(predicate_object_map.object_map.child,row) in join_table[triples_map_element.triples_map_id + "_" + child_list(predicate_object_map.object_map.child)]:
											object_list = join_table[triples_map_element.triples_map_id + "_" + child_list(predicate_object_map.object_map.child)][child_list_value(predicate_object_map.object_map.child,row)]
										else:
											object_list = []
									object = None
								else:
									try:
										object = "<" + string_substitution(triples_map_element.subject_map.value, "{(.+?)}", row, "object") + ">"
									except TypeError:
										object = None
							break
						else:
							continue
				else:
					object = None
			else:
				object = None

			if predicate in general_predicates:
				dictionary_table_update(predicate + "_" + predicate_object_map.object_map.value)
			else:
				dictionary_table_update(predicate)
			if predicate is not None and object is not None and subject is not None:
				dictionary_table_update(subject)
				dictionary_table_update(object)
				for graph in triples_map.subject_map.graph:
					triple = subject + " " + predicate + " " + object + ".\n"
					triple_hdt = dic_table[subject] + " " + dic_table[predicate] + " " + dic_table[object] + ".\n"
					if graph is not None and "defaultGraph" not in graph:
						if "{" in triples_map.subject_map.graph:
							triple = triple[:-2] + " <" + string_substitution(graph, "{(.+?)}", row, "subject") + ">.\n"
							dictionary_table_update("<" + string_substitution(graph, "{(.+?)}", row, "subject") + ">")
						else:
							triple = triple[:-2] + " <" + graph + ">.\n"
							dictionary_table_update("<" + graph + ">")
					
					if duplicate == "yes":
						if predicate in general_predicates:
							if dic_table[predicate + "_" + predicate_object_map.object_map.value] not in g_triples:					
								output_file_descriptor.write(triple)
								if (number_triple + i + 1) % 10000 == 0:
									csv_file.writerow([dataset_name, number_triple + i + 1, time.time()-start_time])
								g_triples.update({dic_table[predicate + "_" + predicate_object_map.object_map.value] : {dic_table[subject] + "_" + dic_table[object]: ""}})
								i += 1
							elif dic_table[subject] + "_" + dic_table[object] not in g_triples[dic_table[predicate + "_" + predicate_object_map.object_map.value]]:
								output_file_descriptor.write(triple)
								if (number_triple + i + 1) % 10000 == 0:
									csv_file.writerow([dataset_name, number_triple + i + 1, time.time()-start_time])
								g_triples[dic_table[predicate + "_" + predicate_object_map.object_map.value]].update({dic_table[subject] + "_" + dic_table[object]: ""})
								i += 1
						else:
							if dic_table[predicate] not in g_triples:					
								output_file_descriptor.write(triple)
								if (number_triple + i + 1) % 10000 == 0:
									csv_file.writerow([dataset_name, number_triple + i + 1, time.time()-start_time])
								g_triples.update({dic_table[predicate] : {dic_table[subject] + "_" + dic_table[object]: ""}})
								i += 1
							elif dic_table[subject] + "_" + dic_table[object] not in g_triples[dic_table[predicate]]:
								output_file_descriptor.write(triple)
								if (number_triple + i + 1) % 10000 == 0:
									csv_file.writerow([dataset_name, number_triple + i + 1, time.time()-start_time])
								g_triples[dic_table[predicate]].update({dic_table[subject] + "_" + dic_table[object]: ""})
								i += 1 
					else:
						output_file_descriptor.write(triple)
						if (number_triple + i + 1) % 10000 == 0:
							csv_file.writerow([dataset_name, number_triple + i + 1, time.time()-start_time])
						i += 1
				if predicate[1:-1] in predicate_object_map.graph:
					triple = subject + " " + predicate + " " + object + ".\n"
					triple_hdt = dic_table[subject] + " " + dic_table[predicate] + " " + dic_table[object] + ".\n"
					if predicate_object_map.graph[predicate[1:-1]] is not None and "defaultGraph" not in predicate_object_map.graph[predicate[1:-1]]:
						if "{" in triples_map.subject_map.graph:
							triple = triple[:-2] + " <" + string_substitution(predicate_object_map.graph[predicate[1:-1]], "{(.+?)}", row, "subject") + ">.\n"
							dictionary_table_update("<" + string_substitution(predicate_object_map.graph[predicate[1:-1]], "{(.+?)}", row, "subject") + ">")
						else:
							triple = triple[:-2] + " <" + predicate_object_map.graph[predicate[1:-1]] + ">.\n"
							dictionary_table_update("<" + predicate_object_map.graph[predicate[1:-1]] + ">")
						
						if duplicate == "yes":
							if predicate in general_predicates:
								if dic_table[predicate + "_" + predicate_object_map.object_map.value] not in g_triples:					
									output_file_descriptor.write(triple)
									if (number_triple + i + 1) % 10000 == 0:
										csv_file.writerow([dataset_name, number_triple + i + 1, time.time()-start_time])
									g_triples.update({dic_table[predicate + "_" + predicate_object_map.object_map.value] : {dic_table[subject] + "_" + dic_table[object]: ""}})
									i += 1
								elif subject + "_" + object not in g_triples[predicate + "_" + predicate_object_map.object_map.value]:
									output_file_descriptor.write(triple)
									if (number_triple + i + 1) % 10000 == 0:
										csv_file.writerow([dataset_name, number_triple + i + 1, time.time()-start_time])
									g_triples[dic_table[predicate + "_" + predicate_object_map.object_map.value]].update({dic_table[subject] + "_" + dic_table[object]: ""})
									i += 1
							else:
								if dic_table[predicate] not in g_triples:					
									output_file_descriptor.write(triple)
									if (number_triple + i + 1) % 10000 == 0:
										csv_file.writerow([dataset_name, number_triple + i + 1, time.time()-start_time])
									g_triples.update({dic_table[predicate] : {dic_table[subject] + "_" + dic_table[object]: ""}})
									i += 1
								elif subject + "_" + object not in g_triples[predicate]:
									output_file_descriptor.write(triple)
									if (number_triple + i + 1) % 10000 == 0:
										csv_file.writerow([dataset_name, number_triple + i + 1, time.time()-start_time])
									g_triples[dic_table[predicate]].update({dic_table[subject] + "_" + dic_table[object]: ""})
									i += 1
						else:
							output_file_descriptor.write(triple)
							if (number_triple + i + 1) % 10000 == 0:
								csv_file.writerow([dataset_name, number_triple + i + 1, time.time()-start_time])

			elif predicate is not None and subject is not None and object_list:
				dictionary_table_update(subject)
				for obj in object_list:
					dictionary_table_update(obj)
					if obj is not None:
						for graph in triples_map.subject_map.graph:
							if predicate_object_map.object_map.term is not None:
								if "IRI" in predicate_object_map.object_map.term:
									triple = subject + " " + predicate + " <" + obj[1:-1] + ">.\n"
								else:
									triple = subject + " " + predicate + " " + obj + ".\n"
							else:
								triple = subject + " " + predicate + " " + obj + ".\n"
							if graph is not None and "defaultGraph" not in graph:
								if "{" in triples_map.subject_map.graph:
									triple = triple[:-2] + " <" + string_substitution(graph, "{(.+?)}", row, "subject") + ">.\n"
									dictionary_table_update("<" + string_substitution(graph, "{(.+?)}", row, "subject") + ">")
								else:
									triple = triple[:-2] + " <" + graph + ">.\n"
									dictionary_table_update("<" + graph + ">")
							if duplicate == "yes":
								
								if predicate in general_predicates:
									if dic_table[predicate + "_" + predicate_object_map.object_map.value] not in g_triples:
										output_file_descriptor.write(triple)
										if (number_triple + i + 1) % 10000 == 0:
											csv_file.writerow([dataset_name, number_triple + i + 1, time.time()-start_time])
										g_triples.update({dic_table[predicate + "_" + predicate_object_map.object_map.value] : {dic_table[subject] + "_" + dic_table[obj]: ""}})
										i += 1
									elif dic_table[subject] + "_" + dic_table[obj] not in g_triples[dic_table[predicate + "_" + predicate_object_map.object_map.value]]:
										output_file_descriptor.write(triple)
										if (number_triple + i + 1) % 10000 == 0:
											csv_file.writerow([dataset_name, number_triple + i + 1, time.time()-start_time])
										g_triples[dic_table[predicate + "_" + predicate_object_map.object_map.value]].update({dic_table[subject] + "_" + dic_table[obj]: ""})
										i += 1
								else:
									if dic_table[predicate] not in g_triples:
										output_file_descriptor.write(triple)
										if (number_triple + i + 1) % 10000 == 0:
											csv_file.writerow([dataset_name, number_triple + i + 1, time.time()-start_time])
										g_triples.update({dic_table[predicate] : {dic_table[subject] + "_" + dic_table[obj]: ""}})
										i += 1
									elif dic_table[subject] + "_" + dic_table[obj] not in g_triples[dic_table[predicate]]:
										output_file_descriptor.write(triple)
										if (number_triple + i + 1) % 10000 == 0:
											csv_file.writerow([dataset_name, number_triple + i + 1, time.time()-start_time])
										g_triples[dic_table[predicate]].update({dic_table[subject] + "_" + dic_table[obj]: ""})
										i += 1

							else:
								output_file_descriptor.write(triple)
								if (number_triple + i + 1) % 10000 == 0:
									csv_file.writerow([dataset_name, number_triple + i + 1, time.time()-start_time])
								i += 1
						if predicate[1:-1] in predicate_object_map.graph:
							if predicate_object_map.object_map.term is not None:
								if "IRI" in predicate_object_map.object_map.term:
									triple = subject + " " + predicate + " <" + obj[1:-1] + ">.\n"
								else:
									triple = subject + " " + predicate + " " + obj + ".\n"
							else:
								triple = subject + " " + predicate + " " + obj + ".\n"
							if predicate_object_map.graph[predicate[1:-1]] is not None and "defaultGraph" not in predicate_object_map.graph[predicate[1:-1]]:
								if "{" in triples_map.subject_map.graph:
									triple = triple[:-2] + " <" + string_substitution(predicate_object_map.graph[predicate[1:-1]], "{(.+?)}", row, "subject") + ">.\n"
									dictionary_table_update("<" + string_substitution(predicate_object_map.graph[predicate[1:-1]], "{(.+?)}", row, "subject") + ">")
								else:
									triple = triple[:-2] + " <" + predicate_object_map.graph[predicate[1:-1]] + ">.\n"
									dictionary_table_update("<" + predicate_object_map.graph[predicate[1:-1]] + ">")
								
								if duplicate == "yes":
									if predicate in general_predicates:
										if dic_table[predicate + "_" + predicate_object_map.object_map.value] not in g_triples:					
											output_file_descriptor.write(triple)
											if (number_triple + i + 1) % 10000 == 0:
												csv_file.writerow([dataset_name, number_triple + i + 1, time.time()-start_time])
											g_triples.update({dic_table[predicate + "_" + predicate_object_map.object_map.value] : {dic_table[subject] + "_" + dic_table[obj]: ""}})
											i += 1
										elif dic_table[subject] + "_" + dic_table[obj] not in g_triples[dic_table[predicate + "_" + predicate_object_map.object_map.value]]:
											output_file_descriptor.write(triple)
											if (number_triple + i + 1) % 10000 == 0:
												csv_file.writerow([dataset_name, number_triple + i + 1, time.time()-start_time])
											g_triples[dic_table[predicate + "_" + predicate_object_map.object_map.value]].update({dic_table[subject] + "_" + dic_table[obj]: ""})
											i += 1
									else:
										if dic_table[predicate] not in g_triples:					
											output_file_descriptor.write(triple)
											if (number_triple + i + 1) % 10000 == 0:
												csv_file.writerow([dataset_name, number_triple + i + 1, time.time()-start_time])
											g_triples.update({dic_table[predicate] : {dic_table[subject] + "_" + dic_table[obj]: ""}})
											i += 1
										elif dic_table[subject] + "_" + dic_table[obj] not in g_triples[dic_table[predicate]]:
											output_file_descriptor.write(triple)
											if (number_triple + i + 1) % 10000 == 0:
												csv_file.writerow([dataset_name, number_triple + i + 1, time.time()-start_time])
											g_triples[dic_table[predicate]].update({dic_table[subject] + "_" + dic_table[obj]: ""})
											i += 1
								else:
									output_file_descriptor.write(triple)
									if (number_triple + i + 1) % 10000 == 0:
										csv_file.writerow([dataset_name, number_triple + i + 1, time.time()-start_time])
									i += 1
				object_list = []
			else:
				continue
	return i

def semantify_mysql(row, row_headers, triples_map, triples_map_list, output_file_descriptor, csv_file, dataset_name, host, port, user, password,dbase):

	"""
	(Private function, not accessible from outside this package)

	Takes a triples-map rule and applies it to each one of the rows of its CSV data
	source

	Parameters
	----------
	triples_map : TriplesMap object
		Mapping rule consisting of a logical source, a subject-map and several predicateObjectMaps
		(refer to the TriplesMap.py file in the triplesmap folder)
	triples_map_list : list of TriplesMap objects
		List of triples-maps parsed from current mapping being used for the semantification of a
		dataset (mainly used to perform rr:joinCondition mappings)
	delimiter : string
		Delimiter value for the CSV or TSV file ("\s" and "\t" respectively)
	output_file_descriptor : file object 
		Descriptor to the output file (refer to the Python 3 documentation)

	Returns
	-------
	An .nt file per each dataset mentioned in the configuration file semantified.
	If the duplicates are asked to be removed in main memory, also returns a -min.nt
	file with the triples sorted and with the duplicates removed.
	"""
	triples_map_triples = {}
	generated_triples = {}
	object_list = []
	subject_value = string_substitution_array(triples_map.subject_map.value, "{(.+?)}", row, row_headers, "subject")
	i = 0
	if duplicate == "yes":
		triple_entry = {subject_value: dictionary_maker_array(row, row_headers)}
		if subject_value in triples_map_triples:
			if shared_items(triples_map_triples[subject_value], triple_entry) == len(triples_map_triples[subject_value]):
				subject = None
			else:
				if triples_map.subject_map.subject_mapping_type == "template":
					if triples_map.subject_map.term_type is None:
						if triples_map.subject_map.condition == "":

							try:
								subject = "<" + subject_value + ">"
								triples_map_triples[subject_value].append(dictionary_maker(row)) 
							except:
								subject = None

						else:
						#	field, condition = condition_separetor(triples_map.subject_map.condition)
						#	if row[field] == condition:
							try:
								subject = "<" + subject_value  + ">"
								triples_map_triples[subject_value].append(dictionary_maker(row)) 
							except:
								subject = None 
					else:
						if "IRI" in triples_map.subject_map.term_type:
							if triples_map.subject_map.condition == "":

								try:
									subject = "<http://example.com/base/" + subject_value + ">"
									triples_map_triples[subject_value].append(dictionary_maker(row)) 
								except:
									subject = None

							else:
							#	field, condition = condition_separetor(triples_map.subject_map.condition)
							#	if row[field] == condition:
								try:
									subject = "<http://example.com/base/" + subject_value + ">"
									triples_map_triples[subject_value].append(dictionary_maker(row)) 
								except:
									subject = None 

						elif "BlankNode" in triples_map.subject_map.term_type:
							if triples_map.subject_map.condition == "":

								try:
									subject = "_:" + subject_value
									triples_map_triples[subject_value].append(dictionary_maker(row)) 
								except:
									subject = None

							else:
							#	field, condition = condition_separetor(triples_map.subject_map.condition)
							#	if row[field] == condition:
								try:
									subject = "_:" + subject_value  
									triples_map_triples[subject_value].append(dictionary_maker(row)) 
								except:
									subject = None
									
						else:
							if triples_map.subject_map.condition == "":

								try:
									subject = "<" + subject_value + ">"
									triples_map_triples.update(triple_entry) 
								except:
									subject = None

							else:
							#	field, condition = condition_separetor(triples_map.subject_map.condition)
							#	if row[field] == condition:
								try:
									subject = "<" + subject_value + ">"
									triples_map_triples.update(triple_entry) 
								except:
									subject = None 
				elif triples_map.subject_map.subject_mapping_type == "reference":
					subject_value = string_substitution_array(triples_map.subject_map.value, ".+", row, row_headers,"subject")
					subject_value = subject_value[1:-1]
					try:
						if " " not in subject_value:
							subject = "<http://example.com/base/" + subject_value + ">"
							triples_map_triples.update(triple_entry)
						else:
							print("<http://example.com/base/" + subject_value + "> is an invalid URL")
							subject = None 
					except:
						subject = None

				elif "constant" in triples_map.subject_map.subject_mapping_type:
					subject = "<" + subject_value + ">"

				else:
					if triples_map.subject_map.condition == "":

						try:
							subject =  "\"" + triples_map.subject_map.value + "\""
							triple_entry = {subject: [dictionary_maker(row)]}	
							triples_map_triples.update(triple_entry) 
						except:
							subject = None

					else:
					#	field, condition = condition_separetor(triples_map.subject_map.condition)
					#	if row[field] == condition:
						try:
							subject =  "\"" + triples_map.subject_map.value + "\""
							triple_entry = {subject: [dictionary_maker(row)]}
							triples_map_triples.update(triple_entry) 
						except:
							subject = None
		else:
			if triples_map.subject_map.subject_mapping_type == "template":
				if triples_map.subject_map.term_type is None:
					if triples_map.subject_map.condition == "":

						try:
							subject = "<" + subject_value + ">"
							triples_map_triples.update(triple_entry) 
						except:
							subject = None

					else:
					#	field, condition = condition_separetor(triples_map.subject_map.condition)
					#	if row[field] == condition:
						try:
							subject = "<" + subject_value  + ">"
							triples_map_triples.update(triple_entry) 
						except:
							subject = None
				else:
					if "IRI" in triples_map.subject_map.term_type:
						if triples_map.subject_map.condition == "":

							try:
								subject = "<http://example.com/base/" + subject_value + ">"
								triples_map_triples.update(triple_entry) 
							except:
								subject = None

						else:
						#	field, condition = condition_separetor(triples_map.subject_map.condition)
						#	if row[field] == condition:
							try:
								subject = "<http://example.com/base/" + subject_value + ">"
								triples_map_triples.update(triple_entry) 
							except:
								subject = None
						
					elif "BlankNode" in triples_map.subject_map.term_type:
						if triples_map.subject_map.condition == "":

							try:
								subject = "_:" + subject_value 
								triples_map_triples.update(triple_entry) 
							except:
								subject = None

						else:
						#	field, condition = condition_separetor(triples_map.subject_map.condition)
						#	if row[field] == condition:
							try:
								subject = "_:" + subject_value 
								triples_map_triples.update(triple_entry) 
							except:
								subject = None
					else:
						if triples_map.subject_map.condition == "":

							try:
								subject = "<" + subject_value + ">"
								triples_map_triples.update(triple_entry) 
							except:
								subject = None

						else:
						#	field, condition = condition_separetor(triples_map.subject_map.condition)
						#	if row[field] == condition:
							try:
								subject = "<" + subject_value + ">"
								triples_map_triples.update(triple_entry) 
							except:
								subject = None

			elif triples_map.subject_map.subject_mapping_type == "reference":
				if triples_map.subject_map.condition == "":
					subject_value = string_substitution_array(triples_map.subject_map.value, ".+", row, row_headers, "subject")
					subject_value = subject_value[1:-1]
					try:
						if " " not in subject_value:
							subject = "<http://example.com/base/" + subject_value + ">"
							triples_map_triples.update(triple_entry)
						else:
							print("<http://example.com/base/" + subject_value + "> is an invalid URL")
							subject = None 
					except:
						subject = None

				else:
				#	field, condition = condition_separetor(triples_map.subject_map.condition)
				#	if row[field] == condition:
					try:
						subject = "<http://example.com/base/" + subject_value + ">"
						triples_map_triples.update(triple_entry) 
					except:
						subject = None

			elif "constant" in triples_map.subject_map.subject_mapping_type:
				subject = "<" + subject_value + ">"

			else:
				if triples_map.subject_map.condition == "":

					try:
						subject =  "\"" + triples_map.subject_map.value + "\""
						triple_entry = {subject: [dictionary_maker(row)]}	
						triples_map_triples.update(triple_entry) 
					except:
						subject = None

				else:
				#	field, condition = condition_separetor(triples_map.subject_map.condition)
				#	if row[field] == condition:
					try:
						subject =  "\"" + triples_map.subject_map.value + "\""
						triple_entry = {subject: [dictionary_maker(row)]}
						triples_map_triples.update(triple_entry) 
					except:
						subject = None

	else:
		if triples_map.subject_map.condition == "":

			try:
				subject = "<" + subject_value  + ">"
			except:
				subject = None

		else:
		#	field, condition = condition_separetor(triples_map.subject_map.condition)
		#	if row[field] == condition:
			try:
				subject = "<" + subject_value  + ">"
			except:
				subject = None

	
	if triples_map.subject_map.rdf_class is not None and subject is not None:
		predicate = "<http://www.w3.org/1999/02/22-rdf-syntax-ns#type>"
		dictionary_table_update(subject)
		dictionary_table_update(predicate)
		for rdf_class in triples_map.subject_map.rdf_class:
			if rdf_class is not None:
				obj = "<{}>".format(rdf_class)
				dictionary_table_update(obj)
				for graph in graph:
					rdf_type = subject + " " + predicate + " " + obj +" .\n"
					
					if graph is not None and "defaultGraph" not in graph:
						if "{" in triples_map.subject_map.graph:	
							rdf_type = rdf_type[:-2] + " <" + string_substitution(graph, "{(.+?)}", row, "subject") + "> .\n"
							dictionary_table_update("<" + string_substitution(graph, "{(.+?)}", row, "subject") + ">")
							rdf_type_ids = rdf_type_ids[:-2] + " " + dic_table["<" + string_substitution(graph, "{(.+?)}", row, "subject") + ">"] + " .\n"
						else:
							rdf_type = rdf_type[:-2] + " <" + graph + "> .\n"
							dictionary_table_update("<" + graph + ">")
							rdf_type_ids = rdf_type_ids[:-2] + " " + dic_table["<" + graph + ">"] + " .\n"
					if duplicate == "yes":
						if dic_table[predicate] not in g_triples:
							try:
								output_file_descriptor.write(rdf_type)
							except:
								output_file_descriptor.write(rdf_type.encode("utf-8"))
							if (number_triple + i + 1) % 10000 == 0:
								csv_file.writerow([dataset_name, number_triple + i + 1, time.time()-start_time])
							g_triples.update({dic_table[predicate]: {dic_table[subject] + "_" + dic_table[obj]: rdf_type_ids}})
							i += 1
						elif dic_table[subject] + "_" + dic_table[obj] not in g_triples[predicate]:
							try:
								output_file_descriptor.write(rdf_type)
							except:
								output_file_descriptor.write(rdf_type.encode("utf-8"))
							if (number_triple + i + 1) % 10000 == 0:
								csv_file.writerow([dataset_name, number_triple + i + 1, time.time()-start_time])
							g_triples[dic_table[predicate]].update({dic_table[subject] + "_" + dic_table[obj]: rdf_type_ids})
							i += 1
				else:
					output_file_descriptor.write(rdf_type)
					if (number_triple + i + 1) % 10000 == 0:
						csv_file.writerow([dataset_name, number_triple + i + 1, time.time()-start_time])
					i += 1



	for predicate_object_map in triples_map.predicate_object_maps_list:
		if predicate_object_map.predicate_map.mapping_type == "constant" or predicate_object_map.predicate_map.mapping_type == "constant shortcut":
			predicate = "<" + predicate_object_map.predicate_map.value + ">"
		elif predicate_object_map.predicate_map.mapping_type == "template":
			if predicate_object_map.predicate_map.condition != "":
				try:
					predicate = "<" + string_substitution_array(predicate_object_map.predicate_map.value, "{(.+?)}", row, row_headers, "predicate") + ">"
				except:
					predicate = None
			else:
				try:
					predicate = "<" + string_substitution_array(predicate_object_map.predicate_map.value, "{(.+?)}", row, row_headers, "predicate") + ">"
				except:
					predicate = None
		elif predicate_object_map.predicate_map.mapping_type == "reference":
			if predicate_object_map.predicate_map.condition != "":
				predicate = string_substitution_array(predicate_object_map.predicate_map.value, ".+", row, row_headers, "predicate")
		else:
			predicate = None

		if predicate_object_map.object_map.mapping_type == "constant" or predicate_object_map.object_map.mapping_type == "constant shortcut":
			if "/" in predicate_object_map.object_map.value:
				object = "<" + predicate_object_map.object_map.value + ">"
			else:
				object = "\"" + predicate_object_map.object_map.value + "\""
		elif predicate_object_map.object_map.mapping_type == "template":
			try:
				if predicate_object_map.object_map.term is None:
					object = "<" + string_substitution_array(predicate_object_map.object_map.value, "{(.+?)}", row, row_headers, "object") + ">"
				elif "IRI" in predicate_object_map.object_map.term:
					object = "<" + string_substitution_array(predicate_object_map.object_map.value, "{(.+?)}", row, row_headers, "object") + ">"
				else:
					object = "\"" + string_substitution_array(predicate_object_map.object_map.value, "{(.+?)}", row, row_headers, "object") + "\""
			except TypeError:
				object = None
		elif predicate_object_map.object_map.mapping_type == "reference":
			object = string_substitution_array(predicate_object_map.object_map.value, ".+", row, row_headers, "object")
			if (predicate_object_map.object_map.language is not None) and (object is not None):
				if "spanish" in predicate_object_map.object_map.language or "es" in predicate_object_map.object_map.language :
					object += "@es"
				elif "english" in predicate_object_map.object_map.language or "en" in predicate_object_map.object_map.language :
					object += "@en"
				elif "IRI" in predicate_object_map.object_map.term:
						if " " not in object:
							object = "<" + object + ">" 
						else:
							print("<" + object + "> is not a valid URL")
							object = None

		elif predicate_object_map.object_map.mapping_type == "parent triples map":
			for triples_map_element in triples_map_list:
				if triples_map_element.triples_map_id == predicate_object_map.object_map.value:
					if (triples_map_element.data_source != triples_map.data_source) or (triples_map_element.tablename != triples_map.tablename):
						if len(predicate_object_map.object_map.child) == 1:
							if triples_map_element.triples_map_id + "_" + predicate_object_map.object_map.child[0] not in join_table:
								if str(triples_map_element.file_format).lower() == "csv" or triples_map_element.file_format == "JSONPath":
									with open(str(triples_map_element.data_source), "r") as input_file_descriptor:
										if str(triples_map_element.file_format).lower() == "csv":
											data = csv.DictReader(input_file_descriptor, delimiter=delimiter)
											hash_maker(data, triples_map_element, predicate_object_map.object_map)
										else:
											data = json.load(input_file_descriptor)
											hash_maker(data[list(data.keys())[0]], triples_map_element, predicate_object_map.object_map)
								elif triples_map_element.file_format == "XPath":
									with open(str(triples_map_element.data_source), "r") as input_file_descriptor:
										child_tree = ET.parse(input_file_descriptor)
										child_root = child_tree.getroot()
										hash_maker_xml(child_root, triples_map_element, predicate_object_map.object_map)								
								else:
									database, query_list = translate_sql(triples_map_element)
									db = connector.connect(host = host, port = int(port), user = user, password = password)
									cursor = db.cursor(buffered=True)
									if database != "None":
										cursor.execute("use " + database)
									else:
										if dbase.lower() != "none":
											cursor.execute("use " + dbase)
									for query in query_list:
										cursor.execute(query)
										data = cursor
									hash_maker_array(cursor, triples_map_element, predicate_object_map.object_map)
							jt = join_table[triples_map_element.triples_map_id + "_" + predicate_object_map.object_map.child[0]]
							if row[row_headers.index(predicate_object_map.object_map.child[0])] is not None:
								object_list = jt[row[row_headers.index(predicate_object_map.object_map.child[0])]]
							object = None
						else:
							if (triples_map_element.triples_map_id + "_" + child_list(predicate_object_map.object_map.child)) not in join_table:
								if str(triples_map_element.file_format).lower() == "csv" or triples_map_element.file_format == "JSONPath":
									with open(str(triples_map_element.data_source), "r") as input_file_descriptor:
										if str(triples_map_element.file_format).lower() == "csv":
											data = csv.DictReader(input_file_descriptor, delimiter=delimiter)
											hash_maker_list(data, triples_map_element, predicate_object_map.object_map)
										else:
											data = json.load(input_file_descriptor)
											if isinstance(data, list):
												hash_maker_list(data, triples_map_element, predicate_object_map.object_map)
											elif len(data) < 2:
												hash_maker_list(data[list(data.keys())[0]], triples_map_element, predicate_object_map.object_map)

								elif triples_map_element.file_format == "XPath":
									with open(str(triples_map_element.data_source), "r") as input_file_descriptor:
										child_tree = ET.parse(input_file_descriptor)
										child_root = child_tree.getroot()
										hash_maker_xml(child_root, triples_map_element, predicate_object_map.object_map)						
								else:
									database, query_list = translate_sql(triples_map_element)
									db = connector.connect(host=host, port=int(port), user=user, password=password)
									cursor = db.cursor(buffered=True)
									if database != "None":
										cursor.execute("use " + database)
									else:
										if dbase.lower() != "none":
											cursor.execute("use " + dbase)
									for query in query_list:
										temp_query = query.split("FROM")
										parent_list = ""
										for parent in predicate_object_map.object_map.parent:
											parent_list += ", `" + parent + "`"
										new_query = temp_query[0] + parent_list + " FROM " + temp_query[1]
										cursor.execute(new_query)
									hash_maker_array_list(cursor, triples_map_element, predicate_object_map.object_map,row_headers)
							if sublist(predicate_object_map.object_map.child,row_headers):
								if child_list_value_array(predicate_object_map.object_map.child,row,row_headers) in join_table[triples_map_element.triples_map_id + "_" + child_list(predicate_object_map.object_map.child)]:
									object_list = join_table[triples_map_element.triples_map_id + "_" + child_list(predicate_object_map.object_map.child)][child_list_value_array(predicate_object_map.object_map.child,row,row_headers)]
								else:
									object_list = []
							object = None
					else:
						try:
							database, query_list = translate_sql(triples_map)
							database2, query_list_origin = translate_sql(triples_map_element)
							db = connector.connect(host = host, port = int(port), user = user, password = password)
							cursor = db.cursor(buffered=True)
							if database != "None":
								cursor.execute("use " + database)
							else:
								if dbase.lower() != "none":
									cursor.execute("use " + dbase)
							for query in query_list:
								for q in query_list_origin:
									query_1 = q.split("FROM")
									query_2 = query.split("SELECT")[1].split("FROM")[0]
									query_new = query_1[0] + " , " + query_2.replace("DISTINCT","") + " FROM " + query_1[1]
									cursor.execute(query_new)
									r_h=[x[0] for x in cursor.description]
									for r in cursor:
										s = string_substitution_array(triples_map.subject_map.value, "{(.+?)}", r, r_h, "subject")
										if subject_value == s:
											object = "<" + string_substitution_array(triples_map_element.subject_map.value, "{(.+?)}", r, r_h, "object") + ">"
						except TypeError:
							object = None
					break
				else:
					continue
		else:
			object = None

		if object is not None and predicate_object_map.object_map.datatype is not None:
			object += "^^<{}>".format(predicate_object_map.object_map.datatype)

		if predicate is not None and object is not None and subject is not None:
			dictionary_table_update(subject)
			dictionary_table_update(predicate)
			dictionary_table_update(object)
			for graph in triples_map.subject_map.graph:
				triple = subject + " " + predicate + " " + object + ".\n"
				
				if graph is not None and "defaultGraph" not in graph:
					if "{" in graph:
						triple = triple[:-2] + " <" + string_substitution_array(graph, "{(.+?)}", row, row_headers,"subject") + ">.\n"
						dictionary_table_update("<" + string_substitution_array(graph, "{(.+?)}", row, row_headers,"subject") + ">")
						triple_hdt = triple_hdt[:-2] + " " + dic_table["<" + string_substitution_array(graph, "{(.+?)}", row, row_headers,"subject") + ">"] + " .\n"
					else:
						triple = triple[:-2] + " <" + graph + ">.\n"
						dictionary_table_update("<" + graph + ">")
						triple_hdt = triple_hdt[:-2] + " " + dic_table["<" + graph + ">"] + " .\n"
				if duplicate == "yes":
					if dic_table[predicate] not in g_triples:
						try:
							output_file_descriptor.write(triple)
						except:
							output_file_descriptor.write(triple.encode("utf-8"))
						if (number_triple + i + 1) % 10000 == 0:
							csv_file.writerow([dataset_name, number_triple + i + 1, time.time()-start_time])
						g_triples.update({dic_table[predicate] : {dic_table[subject] + "_" + dic_table[object]: triple_hdt}})
						i += 1
					elif dic_table[subject] + "_" + dic_table[object] not in g_triples[dic_table[predicate]]:
						try:
							output_file_descriptor.write(triple)
						except:
							output_file_descriptor.write(triple.encode("utf-8"))
						if (number_triple + i + 1) % 10000 == 0:
							csv_file.writerow([dataset_name, number_triple + i + 1, time.time()-start_time])
						g_triples[dic_table[predicate]].update({dic_table[subject] + "_" + dic_table[object]: triple_hdt})
						i += 1
				else:
					try:
						output_file_descriptor.write(triple)
					except:
						output_file_descriptor.write(triple.encode("utf-8"))
					if (number_triple + i + 1) % 10000 == 0:
						csv_file.writerow([dataset_name, number_triple + i + 1, time.time()-start_time])
					i += 1
			if predicate[1:-1] in predicate_object_map.graph:
				triple = subject + " " + predicate + " " + object + ".\n"
				
				if predicate_object_map.graph[predicate[1:-1]] is not None and "defaultGraph" not in predicate_object_map.graph[predicate[1:-1]]:
					if "{" in triples_map.subject_map.graph:
						triple = triple[:-2] + " <" + string_substitution_array(predicate_object_map.graph[predicate[1:-1]], "{(.+?)}", row, row_headers,"subject") + ">.\n"
						dictionary_table_update("<" + string_substitution_array(predicate_object_map.graph[predicate[1:-1]], "{(.+?)}", row, row_headers,"subject") + ">")
						triple_hdt = triple_hdt[:-2] + " " + dic_table["<" + string_substitution_array(predicate_object_map.graph[predicate[1:-1]], "{(.+?)}", row, row_headers,"subject") + ">"] + " .\n"
					else:
						triple = triple[:-2] + " <" + predicate_object_map.graph[predicate[1:-1]] + ">.\n"
						dictionary_table_update("<" + predicate_object_map.graph[predicate[1:-1]] + ">")
						triple_hdt = triple_hdt[:-2] + " " + dic_table["<" + predicate_object_map.graph[predicate[1:-1]] + ">"] + " .\n"
					if duplicate == "yes":
						if dic_table[predicate] not in g_triples:					
							output_file_descriptor.write(triple)
							if (number_triple + i + 1) % 10000 == 0:
								csv_file.writerow([dataset_name, number_triple + i + 1, time.time()-start_time])
							g_triples.update({dic_table[predicate] : {dic_table[subject] + "_" + dic_table[object]: triple_hdt}})
							i += 1
						elif dic_table[subject] + "_" + dic_table[object] not in g_triples[dic_table[predicate]]:
							output_file_descriptor.write(triple)
							if (number_triple + i + 1) % 10000 == 0:
								csv_file.writerow([dataset_name, number_triple + i + 1, time.time()-start_time])
							g_triples[dic_table[predicate]].update({dic_table[subject] + "_" + dic_table[object]: triple_hdt})
							i += 1
					else:
						output_file_descriptor.write(triple)
						if (number_triple + i + 1) % 10000 == 0:
							csv_file.writerow([dataset_name, number_triple + i + 1, time.time()-start_time])
						i += 1
		elif predicate is not None and subject is not None and object_list:
			dictionary_table_update(subject)
			dictionary_table_update(predicate)
			for obj in object_list:
				dictionary_table_update(obj)
				for graph in triples_map.subject_map.graph:
					triple = subject + " " + predicate + " " + obj + ".\n"
					
					if graph is not None and "defaultGraph" not in graph:
						if "{" in graph:
							triple = triple[:-2] + " <" + string_substitution_array(graph, "{(.+?)}", row, row_headers,"subject") + ">.\n"
							dictionary_table_update("<" + string_substitution_array(graph, "{(.+?)}", row, row_headers,"subject") + ">")
							triple_hdt = triple_hdt[:-2] + " " + dic_table["<" + string_substitution_array(graph, "{(.+?)}", row, row_headers,"subject") + ">"] + " .\n"
						else:
							triple = triple[:-2] + " <" + graph + ">.\n"
							dictionary_table_update("<" + graph + ">")
							triple_hdt = triple_hdt[:-2] + " " + dic_table["<" + graph + ">"] + " .\n"

					if duplicate == "yes":
						if dic_table[predicate] not in g_triples:
							try:
								output_file_descriptor.write(triple)
							except:
								output_file_descriptor.write(triple.encode("utf-8"))
							if (number_triple + i + 1) % 10000 == 0:
								csv_file.writerow([dataset_name, number_triple + i + 1, time.time()-start_time])
							g_triples.update({dic_table[predicate] : {dic_table[subject] + "_" + dic_table[obj]: triple_hdt}})
							i += 1
						elif dic_table[subject] + "_" + dic_table[obj] not in g_triples[dic_table[predicate]]:
							try:
								output_file_descriptor.write(triple)
							except:
								output_file_descriptor.write(triple.encode("utf-8"))
							if (number_triple + i + 1) % 10000 == 0:
								csv_file.writerow([dataset_name, number_triple + i + 1, time.time()-start_time])
							g_triples[dic_table[predicate]].update({dic_table[subject] + "_" + dic_table[obj]: triple_hdt})
							i += 1
					else:
						try:
							output_file_descriptor.write(triple)
						except:
							output_file_descriptor.write(triple.encode("utf-8"))
						if (number_triple + i + 1) % 10000 == 0:
							csv_file.writerow([dataset_name, number_triple + i + 1, time.time()-start_time])
						i += 1
				if predicate[1:-1] in predicate_object_map.graph:
					triple = subject + " " + predicate + " " + obj + ".\n"
					
					if predicate_object_map.graph[predicate[1:-1]] is not None and "defaultGraph" not in predicate_object_map.graph[predicate[1:-1]]:
						if "{" in triples_map.subject_map.graph:
							triple = triple[:-2] + " <" + string_substitution_array(predicate_object_map.graph[predicate[1:-1]], "{(.+?)}", row, row_headers,"subject") + ">.\n"
							dictionary_table_update("<" + string_substitution_array(predicate_object_map.graph[predicate[1:-1]], "{(.+?)}", row, row_headers,"subject") + ">")
							triple_hdt = triple_hdt[:-2] + " " + dic_table["<" + string_substitution_array(predicate_object_map.graph[predicate[1:-1]], "{(.+?)}", row, row_headers,"subject") + ">"] + " .\n"
						else:
							triple = triple[:-2] + " <" + predicate_object_map.graph[predicate[1:-1]] + ">.\n"
							dictionary_table_update("<" + predicate_object_map.graph[predicate[1:-1]] + ">")
							triple_hdt = triple_hdt[:-2] + " " + dic_table["<" + predicate_object_map.graph[predicate[1:-1]] + ">"] + " .\n"
						if duplicate == "yes":
							if dic_table[predicate] not in g_triples:					
								output_file_descriptor.write(triple)
								if (number_triple + i + 1) % 10000 == 0:
									csv_file.writerow([dataset_name, number_triple + i + 1, time.time()-start_time])
								g_triples.update({dic_table[predicate] : {dic_table[subject] + "_" + dic_table[obj]: triple_hdt}})
								i += 1
							elif dic_table[subject] + "_" + dic_table[obj] not in g_triples[dic_table[predicate]]:
								output_file_descriptor.write(triple)
								if (number_triple + i + 1) % 10000 == 0:
									csv_file.writerow([dataset_name, number_triple + i + 1, time.time()-start_time])
								generated_triples.update({triple : number_triple})
								g_triples[dic_table[predicate]].update({dic_table[subject] + "_" + dic_table[obj]: triple_hdt})
								i += 1
							elif triple not in g_triples[dic_table[predicate]][dic_table[subject] + "_" + dic_table[obj]]: 
								output_file_descriptor.write(triple)
								if (number_triple + i + 1) % 10000 == 0:
									csv_file.writerow([dataset_name, number_triple + i + 1, time.time()-start_time])
								i += 1
						else:
							output_file_descriptor.write(triple)
							if (number_triple + i + 1) % 10000 == 0:
								csv_file.writerow([dataset_name, number_triple + i + 1, time.time()-start_time])
							i += 1
			object_list = []
		else:
			continue
	return i

def semantify(config_path):

	if os.path.isfile(config_path) == False:
		print("The configuration file " + config_path + " does not exist.")
		print("Aborting...")
		sys.exit(1)

	config = ConfigParser(interpolation=ExtendedInterpolation())
	config.read(config_path)

	global duplicate
	duplicate = config["datasets"]["remove_duplicate"]

	enrichment = config["datasets"]["enrichment"]

	if not os.path.exists(config["datasets"]["output_folder"]):
		os.mkdir(config["datasets"]["output_folder"])

	start_time = time.time()
	#tracemalloc.start()

	with open(config["datasets"]["output_folder"] + "/" +  config["datasets"]["name"] + "_datasets_stats.csv", 'w') as myfile:
		wr = csv.writer(myfile, quoting=csv.QUOTE_ALL)
		wr.writerow(["Dataset", "Number of the triple", "Time"])

		with ThreadPoolExecutor(max_workers=10) as executor:
			for dataset_number in range(int(config["datasets"]["number_of_datasets"])):
				dataset_i = "dataset" + str(int(dataset_number) + 1)
				triples_map_list = mapping_parser(config[dataset_i]["mapping"])
				output_file = config["datasets"]["output_folder"] + "/" + config[dataset_i]["name"] + ".nt"

				print("Semantifying {}...".format(config[dataset_i]["name"]))
				
				with open(output_file, "w", encoding = "utf-8") as output_file_descriptor:
					sorted_sources, predicate_list, order_list = files_sort(triples_map_list, config["datasets"]["ordered"])
					if sorted_sources:
						global number_triple
						if order_list:
							for source_type in order_list:
								if source_type == "csv":
									for source in order_list[source_type]:
										if config["datasets"]["large_file"].lower() == "false":
											reader = pd.read_csv(source)
											reader = reader.where(pd.notnull(reader), None)
											if duplicate == "yes":
												reader = reader.drop_duplicates(keep ='first')
											data = reader.to_dict(orient='records')
											for triples_map in sorted_sources[source_type][source]:
												number_triple += executor.submit(semantify_file, sorted_sources[source_type][source][triples_map], triples_map_list, ",", output_file_descriptor, wr, config[dataset_i]["name"], data).result()
												#current, peak = tracemalloc.get_traced_memory()
												#print("Current memory usage is " + str(current / 10**6) + "MB; Peak was " + str(peak / 10**6) + "MB")
												for po in sorted_sources[source_type][source][triples_map].predicate_object_maps_list:
													if po.predicate_map.value in general_predicates:
														if po.predicate_map.value in predicate_list:
															predicate_list[po.predicate_map.value + "_" + po.object_map.value] -= 1
															if predicate_list[po.predicate_map.value + "_" + po.object_map.value] == 0:
																predicate_list.pop(po.predicate_map.value + "_" + po.object_map.value)
																resource = "<" + po.predicate_map.value + ">" + "_" + po.object_map.value
																if resource in dic_table:
																	if dic_table[resource] in g_triples:
																		g_triples.pop(dic_table[resource])
													else:
														if po.predicate_map.value in predicate_list:
															predicate_list[po.predicate_map.value] -= 1
															if predicate_list[po.predicate_map.value] == 0:
																predicate_list.pop(po.predicate_map.value)
																resource = "<" + po.predicate_map.value + ">"
																if resource in dic_table:
																	if dic_table[resource] in g_triples:
																		g_triples.pop(dic_table[resource])
												if sorted_sources[source_type][source][triples_map].subject_map.rdf_class is not None:
													for rdf_type in sorted_sources[source_type][source][triples_map].subject_map.rdf_class:
														resource = "http://www.w3.org/1999/02/22-rdf-syntax-ns#type" + "_" + "<{}>".format(rdf_type)
														if resource in predicate_list:
															predicate_list[resource] -= 1
															if predicate_list[resource] == 0:
																predicate_list.pop(resource)
																rdf_class = "<http://www.w3.org/1999/02/22-rdf-syntax-ns#type>" + "_" + "<{}>".format(rdf_type)
																if rdf_class in dic_table:
																	if dic_table[rdf_class] in g_triples:
																		g_triples.pop(dic_table[rdf_class])
												#current, peak = tracemalloc.get_traced_memory()
												#print("Current memory usage is " + str(current / 10**6) + "MB; Peak was " + str(peak / 10**6) + "MB")	
										else:
											with open(source, "r") as input_file_descriptor:
												data = csv.DictReader(input_file_descriptor, delimiter=',') 
												for triples_map in sorted_sources[source_type][source]:
													number_triple += executor.submit(semantify_file, sorted_sources[source_type][source][triples_map], triples_map_list, ",", output_file_descriptor, wr, config[dataset_i]["name"], data).result()
													#current, peak = tracemalloc.get_traced_memory()
													#print("Current memory usage is " + str(current / 10**6) + "MB; Peak was " + str(peak / 10**6) + "MB")
													for po in sorted_sources[source_type][source][triples_map].predicate_object_maps_list:
														if po.predicate_map.value in general_predicates:
															if po.predicate_map.value in predicate_list:
																predicate_list[po.predicate_map.value + "_" + po.object_map.value] -= 1
																if predicate_list[po.predicate_map.value + "_" + po.object_map.value] == 0:
																	predicate_list.pop(po.predicate_map.value + "_" + po.object_map.value)
																	resource = "<" + po.predicate_map.value + ">" + "_" + po.object_map.value
																	if resource in dic_table:
																		if dic_table[resource] in g_triples:
																			g_triples.pop(dic_table[resource])
														else:
															if po.predicate_map.value in predicate_list:
																predicate_list[po.predicate_map.value] -= 1
																if predicate_list[po.predicate_map.value] == 0:
																	predicate_list.pop(po.predicate_map.value)
																	resource = "<" + po.predicate_map.value + ">"
																	if resource in dic_table:
																		if dic_table[resource] in g_triples:
																			g_triples.pop(dic_table[resource])
													if sorted_sources[source_type][source][triples_map].subject_map.rdf_class is not None:
														for rdf_type in sorted_sources[source_type][source][triples_map].subject_map.rdf_class:
															resource = "http://www.w3.org/1999/02/22-rdf-syntax-ns#type" + "_" + "<{}>".format(rdf_type)
															if resource in predicate_list:
																predicate_list[resource] -= 1
																if predicate_list[resource] == 0:
																	predicate_list.pop(resource)
																	rdf_class = "<http://www.w3.org/1999/02/22-rdf-syntax-ns#type>" + "_" + "<{}>".format(rdf_type)
																	if rdf_class in dic_table:
																		if dic_table[rdf_class] in g_triples:
																			g_triples.pop(dic_table[rdf_class])
													#current, peak = tracemalloc.get_traced_memory()
													#print("Current memory usage is " + str(current / 10**6) + "MB; Peak was " + str(peak / 10**6) + "MB")	
						else:
							for source_type in sorted_sources:
								if source_type == "csv":
									for source in sorted_sources[source_type]:
										if config["datasets"]["large_file"].lower() == "false":
											reader = pd.read_csv(source)
											reader = reader.where(pd.notnull(reader), None)
											if duplicate == "yes":
												reader = reader.drop_duplicates(keep ='first')
											data = reader.to_dict(orient='records')
											for triples_map in sorted_sources[source_type][source]:
												number_triple += executor.submit(semantify_file, sorted_sources[source_type][source][triples_map], triples_map_list, ",", output_file_descriptor, wr, config[dataset_i]["name"], data).result()
												#current, peak = tracemalloc.get_traced_memory()
												#print("Current memory usage is " + str(current / 10**6) + "MB; Peak was " + str(peak / 10**6) + "MB")
												for po in sorted_sources[source_type][source][triples_map].predicate_object_maps_list:
													if po.predicate_map.value in general_predicates:
														if po.predicate_map.value in predicate_list:
															predicate_list[po.predicate_map.value + "_" + po.object_map.value] -= 1
															if predicate_list[po.predicate_map.value + "_" + po.object_map.value] == 0:
																predicate_list.pop(po.predicate_map.value + "_" + po.object_map.value)
																resource = "<" + po.predicate_map.value + ">" + "_" + po.object_map.value
																if resource in dic_table:
																	if dic_table[resource] in g_triples:
																		g_triples.pop(dic_table[resource])
													else:
														if po.predicate_map.value in predicate_list:
															predicate_list[po.predicate_map.value] -= 1
															if predicate_list[po.predicate_map.value] == 0:
																predicate_list.pop(po.predicate_map.value)
																resource = "<" + po.predicate_map.value + ">"
																if resource in dic_table:
																	if dic_table[resource] in g_triples:
																		g_triples.pop(dic_table[resource])
												if sorted_sources[source_type][source][triples_map].subject_map.rdf_class is not None:
													for rdf_type in sorted_sources[source_type][source][triples_map].subject_map.rdf_class:
														resource = "http://www.w3.org/1999/02/22-rdf-syntax-ns#type" + "_" + "<{}>".format(rdf_type)
														if resource in predicate_list:
															predicate_list[resource] -= 1
															if predicate_list[resource] == 0:
																predicate_list.pop(resource)
																rdf_class = "<http://www.w3.org/1999/02/22-rdf-syntax-ns#type>" + "_" + "<{}>".format(rdf_type)
																if rdf_class in dic_table:
																	if dic_table[rdf_class] in g_triples:
																		g_triples.pop(dic_table[rdf_class])
												#current, peak = tracemalloc.get_traced_memory()
												#print("Current memory usage is " + str(current / 10**6) + "MB; Peak was " + str(peak / 10**6) + "MB")	
										else:
											with open(source, "r") as input_file_descriptor:
												data = csv.DictReader(input_file_descriptor, delimiter=',') 
												for triples_map in sorted_sources[source_type][source]:
													number_triple += executor.submit(semantify_file, sorted_sources[source_type][source][triples_map], triples_map_list, ",", output_file_descriptor, wr, config[dataset_i]["name"], data).result()
													#current, peak = tracemalloc.get_traced_memory()
													#print("Current memory usage is " + str(current / 10**6) + "MB; Peak was " + str(peak / 10**6) + "MB")
													for po in sorted_sources[source_type][source][triples_map].predicate_object_maps_list:
														if po.predicate_map.value in general_predicates:
															if po.predicate_map.value in predicate_list:
																predicate_list[po.predicate_map.value + "_" + po.object_map.value] -= 1
																if predicate_list[po.predicate_map.value + "_" + po.object_map.value] == 0:
																	predicate_list.pop(po.predicate_map.value + "_" + po.object_map.value)
																	resource = "<" + po.predicate_map.value + ">" + "_" + po.object_map.value
																	if resource in dic_table:
																		if dic_table[resource] in g_triples:
																			g_triples.pop(dic_table[resource])
														else:
															if po.predicate_map.value in predicate_list:
																predicate_list[po.predicate_map.value] -= 1
																if predicate_list[po.predicate_map.value] == 0:
																	predicate_list.pop(po.predicate_map.value)
																	resource = "<" + po.predicate_map.value + ">"
																	if resource in dic_table:
																		if dic_table[resource] in g_triples:
																			g_triples.pop(dic_table[resource])
													if sorted_sources[source_type][source][triples_map].subject_map.rdf_class is not None:
														for rdf_type in sorted_sources[source_type][source][triples_map].subject_map.rdf_class:
															resource = "http://www.w3.org/1999/02/22-rdf-syntax-ns#type" + "_" + "<{}>".format(rdf_type)
															if resource in predicate_list:
																predicate_list[resource] -= 1
																if predicate_list[resource] == 0:
																	predicate_list.pop(resource)
																	rdf_class = "<http://www.w3.org/1999/02/22-rdf-syntax-ns#type>" + "_" + "<{}>".format(rdf_type)
																	if rdf_class in dic_table:
																		if dic_table[rdf_class] in g_triples:
																			g_triples.pop(dic_table[rdf_class])
													#current, peak = tracemalloc.get_traced_memory()
													#print("Current memory usage is " + str(current / 10**6) + "MB; Peak was " + str(peak / 10**6) + "MB")	
					if predicate_list:
						for triples_map in triples_map_list:
							if str(triples_map.file_format).lower() != "csv" and triples_map.file_format == "JSONPath" and triples_map.file_format == "XPath":
								if config["datasets"]["dbType"] == "mysql":
									database, query_list = translate_sql(triples_map)
									db = connector.connect(host = config[dataset_i]["host"], port = int(config[dataset_i]["port"]), user = config[dataset_i]["user"], password = config[dataset_i]["password"])
									cursor = db.cursor(buffered=True)
									if database != "None":
										cursor.execute("use " + database)
									else:
										if config[dataset_i]["db"].lower() != "none":
											cursor.execute("use " + config[dataset_i]["db"])
									if triples_map.query == "None":	
										for query in query_list:
											cursor.execute(query)
											row_headers=[x[0] for x in cursor.description]
											for row in cursor:
												if config[dataset_i]["db"].lower() != "none":
													number_triple += executor.submit(semantify_mysql, row, row_headers, triples_map, triples_map_list, output_file_descriptor, wr, config[dataset_i]["name"], config[dataset_i]["host"], int(config[dataset_i]["port"]), config[dataset_i]["user"], config[dataset_i]["password"],config[dataset_i]["db"]).result()
												else:
													number_triple += executor.submit(semantify_mysql, row, row_headers, triples_map, triples_map_list, output_file_descriptor, wr, config[dataset_i]["name"], config[dataset_i]["host"], int(config[dataset_i]["port"]), config[dataset_i]["user"], config[dataset_i]["password"],"None").result()
									else:
										cursor.execute(triples_map.query)
										row_headers=[x[0] for x in cursor.description]
										for row in cursor:
											if config[dataset_i]["db"].lower() != "none":
												number_triple += executor.submit(semantify_mysql, row, row_headers, triples_map, triples_map_list, output_file_descriptor, wr, config[dataset_i]["name"], config[dataset_i]["host"], int(config[dataset_i]["port"]), config[dataset_i]["user"], config[dataset_i]["password"],config[dataset_i]["db"]).result()
											else:
												number_triple += executor.submit(semantify_mysql, row, row_headers, triples_map, triples_map_list, output_file_descriptor, wr, config[dataset_i]["name"], config[dataset_i]["host"], int(config[dataset_i]["port"]), config[dataset_i]["user"], config[dataset_i]["password"],"None").result()
		#tracemalloc.stop()
		print(time.time() - start_time)
