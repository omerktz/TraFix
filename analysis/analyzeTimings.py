import xlrd
import matplotlib.pyplot as plt
from matplotlib import cm
from matplotlib.ticker import LinearLocator, FormatStrFormatter
import numpy as np

fields = [('Training Time', float, 2), ('Overall Training Epochs', int, 3), ('Best Epoch', int, 4),
		  ('Best Dev Bleu Score', float, 5), ('Translation Time', float, 6), ('Evaluation Blue Score', float, 7),
		  ('Successes', int, 8), ('UnParsable', int, 9), ('Failures', int, 10)]


def load_sheet(sheet):
	data = {}
	for row_idx in range(1, sheet.nrows):
		max_num = int(sheet.cell(row_idx, 0).value)
		dataset_size = int(sheet.cell(row_idx, 1).value)
		if max_num not in data.keys():
			data[max_num] = {}
		data[max_num][dataset_size] = map(lambda x: x[1](sheet.cell(row_idx, x[2]).value), fields)
	return data


def load_workbook(workbook_name):
	xl_workbook = xlrd.open_workbook(workbook_name)
	data = {}
	for s in xl_workbook.sheets():
		data[s.name] = load_sheet(s)
	return data


def print_heatmap(data, index):
	X = sorted(data.keys())
	Y = sorted(data[X[0]].keys(), reverse=True)
	Z = map(lambda a: map(lambda b: data[b][a][index], X), Y)
	plt.figure(figsize=(15, 10))
	plt.imshow(Z)
	plt.xticks(range(10))
	plt.yticks(range(10))
	plt.xlabel('Max Number')
	plt.ylabel('Dataset Size')
	plt.title(fields[index][0])
	plt.gca().set_xticklabels(X)
	plt.gca().set_yticklabels(Y)
	plt.colorbar()
	plt.show()


def print_3d_surface(data, index):
	X = sorted(data.keys())
	Y = sorted(data[X[0]].keys(), reverse=True)
	X2, Y2 = np.meshgrid(X, Y)
	Z = map(lambda a: map(lambda b: data[a][b][index], Y), X)
	Z = np.asarray(map(lambda x: np.asarray(x), Z))
	fig = plt.figure(figsize=(15, 10))
	ax = fig.gca(projection='3d')
	plt.xticks(range(10))
	plt.yticks(range(10))
	surf = ax.plot_surface(X2, Y2, Z, cmap=cm.coolwarm, linewidth=0, antialiased=False)
	ax.zaxis.set_major_locator(LinearLocator(10))
	ax.zaxis.set_major_formatter(FormatStrFormatter('%.02f'))
	ax.set_xticks(X)
	ax.set_yticks(Y)
	fig.colorbar(surf, shrink=0.5, aspect=5)
	plt.xlabel('Max Number')
	plt.ylabel('Dataset Size')
	plt.title(fields[index][0])
	plt.show()


def plot(workbook, sheet, index, print3d):
	data = load_workbook(workbook)[sheet]
	if print3d:
		print_3d_surface(data, index)
	else:
		print_heatmap(data, index)


def print_sheets(workbook):
	xl_workbook = xlrd.open_workbook(workbook)
	print 'Available sheets:'
	for s in xl_workbook.sheets():
		print '\t' + s.name


def print_fields():
	print 'Available fields:'
	for i in range(len(fields)):
		print '\t' + str(i) + ') ' + fields[i][0]


if __name__ == "__main__":
	import argparse


	def handle_fields(args):
		print_fields()


	def handle_sheets(args):
		print_sheets(args.workbook)


	def handle_plot(args):
		plot(args.workbook, args.sheet, args.index, args.d)


	parser = argparse.ArgumentParser(description="Analyze timing data")
	subparsers = parser.add_subparsers()
	parser_plot = subparsers.add_parser('plot', help='plot measurements')
	parser_plot.add_argument('workbook', type=str, help="excel workbook file containing measurements")
	parser_plot.add_argument('sheet', type=str, help="sheet to use")
	parser_plot.add_argument('index', type=int, help="index of field to plot")
	parser_plot.add_argument('-3', dest='d', help="print as 3d surface (instead of heatmap)", action='count')
	parser_plot.set_defaults(func=handle_plot)
	parser_fields = subparsers.add_parser('fields', help='print available fields and indexes')
	parser_fields.set_defaults(func=handle_fields)
	parser_sheets = subparsers.add_parser('sheets', help='print available sheet names')
	parser_sheets.add_argument('workbook', type=str, help="excel workbook file containing measurements")
	parser_sheets.set_defaults(func=handle_sheets)
	args = parser.parse_args()
	args.func(args)
