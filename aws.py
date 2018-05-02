import boto3
import paramiko
import os
import sys
import multiprocessing
import shutil
import time
import logging
from utils.colored_logger_with_timestamp import init_colorful_root_logger


class AWShandler:
	def __init__(self, compiler, output, index, image='ami-9c2198e3', username='ubuntu', key='omer1.pem',
				 instance_type='p2.xlarge', security_group='omer-sg', termination_protection=True,
				 instance_name='omer-{0}-{1}', main_dir='Codenator', retries=5):
		self._index = index
		self._ami_id = image
		self._instance_username = username
		self._key_filename = key
		self._compiler = compiler
		self._output = output
		self._instance_type = instance_type
		self._security_group = security_group
		self._termination_protection = termination_protection
		self._instance_name = instance_name
		self._main_dir = main_dir
		self._retries = retries

		self._ec2 = boto3.resource('ec2')
		self._ec2client = boto3.client('ec2')

	def log_info(self, msg):
		logging.info('Instance #{0}: {1}'.format(self._index, msg))
	def log_debug(self, msg):
		logging.debug('Instance #{0}: {1}'.format(self._index, msg))
	def log_error(self, msg):
		logging.error('Instance #{0}: {1}'.format(self._index, msg))

	def create_instance(self):
		self.log_info('Creating instance')
		instance = self._ec2.create_instances(ImageId=self._ami_id, MinCount=1, MaxCount=1, EbsOptimized=True,
											  InstanceType=self._instance_type, SecurityGroups=[self._security_group],
											  DisableApiTermination=self._termination_protection,
											  KeyName=self._key_filename[:self._key_filename.rfind('.')])[0]
		instance.create_tags(Tags=[{'Key': 'Name', 'Value': self._instance_name.format(self._compiler[:-7], self._index)}])
		instance.wait_until_running()
		status = instance.state
		while (status['Code'] != 16) or (status['Name'] != 'running'):
			status = instance.state
		self.log_info('Instance id: {0}'.format(instance.id))
		return instance


	def get_client(self):
		dns = self._ec2client.describe_instances(InstanceIds=[self._instance.id])['Reservations'][0]['Instances'][0]['PublicDnsName']
		self.log_info('Connecting to instance')
		client = paramiko.SSHClient()
		client.set_missing_host_key_policy(paramiko.AutoAddPolicy)
		retry = 0;
		while True:
			try:
				time.sleep(5)
				client.connect(dns, username=self._instance_username, key_filename=self._key_filename)
				break
			except:
				retry += 1
				if retry > self._retries:
					self.log_error('Unable to connect to instance!')
					self.kill_instance()
					sys.exit(1)
				self.log_debug('Connetion failed, retrying ({0}/{1})'.format(retry, self._retries))
		self.log_info('Connection successful')
		return client

	def exec_instance(self):
		self.log_info('Updating code')
		self._client.exec_command('cd {0}; git pull'.format(self._main_dir))
		self.log_info('Executing experiment')
		self._client.exec_command('cd {0}; ./runExperiment.sh output{1} log{1} {2}'.format(self._main_dir, self._index, self._compiler))

	def download_from_instance(self):
		self.log_info('Downloading results')
		sftp = self._client.open_sftp()
		sftp.chdir(self._main_dir)
		sftp.get('output{0}.tar.gz'.format(self._index), os.path.join(self._output, 'output{0}.tar.gz'.format(self._index)))
		os.system('cd {0}; tar -xzf output{1}.tar.gz --warning=no-timestamp ; cd - > /dev/null'.format(self._output, self._index))


	def kill_instance(self):
		self.log_info('Killing instance')
		self._instance.modify_attribute(DisableApiTermination={'Value': False})
		self._instance.terminate()
		# self._instance.wait_until_terminated()


	def launch_instance(self):
		self._instance = self.create_instance()
		self._client = self.get_client()
		self.exec_instance()
		self.download_from_instance()
		self._client.close()
		self.kill_instance()


def instance_wrapper((args, i)):
	def hide_logs():
		logging.getLogger("paramiko").setLevel(logging.WARNING)
		logging.getLogger("boto3").setLevel(logging.WARNING)
		logging.getLogger("botocore").setLevel(logging.WARNING)

	init_colorful_root_logger(logging.getLogger(''), vars(args))
	hide_logs()
	AWShandler(args.compiler, args.output, i, image=args.image, username=args.username, key=args.key,
			   instance_type=args.type, security_group=args.security, termination_protection=args.protection,
			   instance_name=args.naming, main_dir=args.main).launch_instance()

if __name__ == "__main__":
	import argparse

	parser = argparse.ArgumentParser(description="Execute experiments of AWS instances")
	parser.add_argument('count', type=int, help="number of instances")
	parser.add_argument('output', type=str, help="Output directory")
	parser.add_argument('compiler', type=str, help="file containing implementation of 'compiler' function")
	parser.add_argument('-i', '--image', type=str, default='ami-9c2198e3',
						help="AWS image id (default: \'%(default)s\')")
	parser.add_argument('-u', '--username', type=str, default='ubuntu',
						help="instance user name (default: \'%(default)s\')")
	parser.add_argument('-k', '--key', type=str, default='omer1.pem',
						help="key filename (default: \'%(default)s)\'")
	parser.add_argument('-t', '--type', type=str, default='p2.xlarge',
						help="AWS instance type (default: \'%(default)s)\'")
	parser.add_argument('-s', '--security', type=str, default='omer-sg',
						help="AWS security group for instances (default: \'%(default)s)\'")
	parser.add_argument('-n', '--naming', type=str, default='omer-{0}-{1}',
						help="naming pattern for instances (default: \'%(default)s)\'")
	parser.add_argument('-m', '--main', type=str, default='Codenator',
						help="name of main directory on instace (default: \'%(default)s)\'")
	parser.add_argument('-p', '--protection', type=bool, default=False,
						help="apply termination protection (default: %(default)s)")
	parser.add_argument('-r', '--retries', type=int, default=5,
						help="number of attempts to connect to instance (default: %(default)s)")
	parser.add_argument('-v', '--verbose', action='store_const', const=True, help='Be verbose')
	parser.add_argument('--debug', action='store_const', const=True, help='Enable debug prints')
	args = parser.parse_args()

	if os.path.exists(args.output):
		shutil.rmtree(args.output)
	os.makedirs(args.output)

	pool = multiprocessing.Pool(processes=args.count)
	pool.map(instance_wrapper, map(lambda i: (args, i), range(args.count)))
	pool.close()


