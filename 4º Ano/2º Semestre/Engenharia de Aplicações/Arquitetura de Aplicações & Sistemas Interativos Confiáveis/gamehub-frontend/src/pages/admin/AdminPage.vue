<template>


<div class="q-pa-md">
    <div class="q-gutter-y-md" style="max-width: 100%">
      <q-tabs
        dense
        no-caps
        inline-label
        class="bg-black text-white shadow-2"
        v-model="tab"
      >
        <q-tab name="pubMult" icon="photo" label="Publicações Multimedia" @click="changeTab('pubMult')"/>
        <q-tab name="pubGrup" icon="group" label="Publicações Grupo" @click="changeTab('pubGrup')"/>
        <q-tab name="Utili" icon="face" label="Utilizadores" @click="changeTab('Utili')"/>
      </q-tabs>
    </div>
</div>


<div class="q-pa-md">
    <div class="q-gutter-md row items-start">
    
      <q-input v-model="search" filled type="search" hint="Identificador">
        <template v-slot:append>
          <q-icon name="search" />
        </template>
      </q-input>

      <q-input v-model="email" filled type="email" hint="Nome do utilizador" >
        <template v-slot:append>
          <q-icon name="search" />
        </template>
      </q-input>

      <q-input v-model="date" filled type="date" hint="Data de inicio" v-if="tab!='Utili'"/>

      <q-input v-model="dateFinal" filled type="date" hint="Data final" v-if="tab!='Utili'"/>
    </div>
</div>


<div class="q-pa-md" v-if="tab=='pubMult'" >
    <q-table
      title=""
      virtual-scroll-horizontal
      :rows="rows_filtered"
      :columns="columns_Multimedia"
    >
        <template v-slot:body="props">

            <q-tr :props="props" >

                <q-td key="close" :props="props">
                    <q-btn :loading="loading[props.row.id]" color="red" @click="persistent = true; id= props.row.id" label="Remover" />
                </q-td>

                <q-td key="id" :props="props">
                    {{ props.row.id }}
                </q-td>
                
                <q-td key="jogo" :props="props">
                    {{ props.row.jogo }}
                </q-td>

                <q-td key="descricao" :props="props">
                    {{ props.row.descricao }}
                </q-td>

                <q-td key="datetime" :props="props">
                    {{ props.row.datetime }}
                </q-td>

                <q-td key="multimedia" :props="props">
                    <button class="btn btn-success" @click="openNewTab(props.row.multimedia)">Ver</button>
                </q-td>

                <q-td key="gamer_id" :props="props">
                    {{ props.row.gamer_id }}
                </q-td>

                <q-td key="gamer_nome" :props="props">
                    {{ props.row.gamer_nome }}
                </q-td>
            </q-tr>
        </template>

    </q-table>
</div>

<div class="q-pa-md" v-if="tab=='pubGrup'">
    <q-table
      title=""
      :rows="rows_filtered"
      :columns="columns_Grupo"
    >
        <template v-slot:body="props">

            <q-tr :props="props">

                <q-td key="close" :props="props">
                    <q-btn :loading="loading[props.row.id]" color="red" @click="persistent = true; id= props.row.id" label="Remover" />
                </q-td>

                <q-td key="id" :props="props">
                    {{ props.row.id }}
                </q-td>
                
                <q-td key="jogo" :props="props">
                    {{ props.row.jogo }}
                </q-td>

                <q-td key="descricao" :props="props">
                    {{ props.row.descricao }}
                </q-td>

                <q-td key="datetime" :props="props">
                    {{ props.row.datetime }}
                </q-td>

                <q-td key="gamer_id" :props="props">
                    {{ props.row.gamer_id }}
                </q-td>

                <q-td key="gamer_nome" :props="props">
                    {{ props.row.gamer_nome }}
                </q-td>
            </q-tr>
        </template>

    </q-table>
</div>

<div class="q-pa-md" v-if="tab=='Utili'">
    <q-table
      title=""
      :rows="rows_filtered"
      :columns="columns_Utilizador"
    >
        <template v-slot:body="props">

            <q-tr :props="props">

                <q-td key="close" :props="props">
                    <q-btn :loading="loading[props.row.id]" color="red" @click="persistent = true; id= props.row.id" label="Banir" />
                </q-td>

                <q-td key="id" :props="props">
                    {{ props.row.id }}
                </q-td>
                
                <q-td key="nome" :props="props">
                    {{ props.row.nome }}
                </q-td>

                <q-td key="classificacao" :props="props"> 
                    <q-badge :color="props.row.classificacao<2?'red':'green'" >
                        {{ props.row.classificacao }}
                    </q-badge>
                </q-td>

                <q-td key="avatar" :props="props">
                    <button class="btn btn-success" @click="openNewTab(props.row.avatar)">Ver</button>
                </q-td>

            </q-tr>
        </template>

    </q-table>
</div>

<div class="q-pa-md q-gutter-sm">
    <q-dialog v-model="persistent" persistent transition-show="scale" transition-hide="scale">
      <q-card class="bg-teal text-white" style="width: 300px">
        <q-card-section>
          <div class="text-h6">Tem certeza que pretende remover?</div>
        </q-card-section>

        <q-card-actions align="right" class="bg-white text-teal">
          <q-btn flat label="Não remover" v-close-popup />
          <q-btn flat label="Remover" v-close-popup @click="simulateProgress();"/>
        </q-card-actions>
      </q-card>
    </q-dialog>
</div>

</template>

<script>

import { ref } from 'vue';
import { computed, onMounted } from "@vue/runtime-core";
import axios from "axios";
import URL from "../../url.js";
import { useQuasar } from "quasar";

const columns_Multimedia = [
  { name: 'close', align: 'center', label: '', field: 'close'},
  { name: 'id', align: 'center', label: 'Identificador', field: 'id', sortable: true },
  { name: 'jogo', align: 'center', label: 'Nome do Jogo', field: 'jogo', sortable: true },
  { name: 'descricao', align: 'center', label: 'Descrição', field: 'descricao', sortable: true},
  { name: 'datetime', align: 'center', label: 'Data de publicação', field: 'datetime', sortable: true },
  { name: 'multimedia', align: 'center', label: 'Link da media', field: 'multimedia', sortable: true },
  { name: 'gamer_id', align: 'center', label: 'Identificador do gamer', field: 'gamer_id', sortable: true },
  { name: 'gamer_nome', align: 'center', label: 'Nome do gamer', field: 'gamer_nome', sortable: true }
]

const columns_Grupo = [
  { name: 'close', align: 'center', label: '', field: 'close'},
  { name: 'id', align: 'center', label: 'Identificador', field: 'id', sortable: true },
  { name: 'jogo', align: 'center', label: 'Nome do Jogo', field: 'jogo', sortable: true },
  { name: 'descricao', align: 'center', label: 'Descrição', field: 'descricao', sortable: true},
  { name: 'datetime', align: 'center', label: 'Data de publicação', field: 'datetime', sortable: true },
  { name: 'gamer_id', align: 'center', label: 'Identificador do gamer', field: 'gamer_id', sortable: true },
  { name: 'gamer_nome', align: 'center', label: 'Nome do gamer', field: 'gamer_nome', sortable: true }
]

const columns_Utilizador = [
  { name: 'close', align: 'center', label: '', field: 'close'},
  { name: 'id', align: 'center', label: 'Identificador', field: 'id', sortable: true },
  { name: 'nome', align: 'center', label: 'Nome do Gamer', field: 'jogo', sortable: true },
  { name: 'classificacao', align: 'center', label: 'Classificação', field: 'descricao', sortable: true, sort: (a, b) => parseFloat(b) > parseFloat(a)},
  { name: 'avatar', align: 'center', label: 'Avatar', field: 'datetime', sortable: true }
]

export default {

  setup () {

    var dates = {
        convert:function(d) {
            // Converts the date in d to a date-object. The input can be:
            //   a date object: returned without modification
            //  an array      : Interpreted as [year,month,day]. NOTE: month is 0-11.
            //   a number     : Interpreted as number of milliseconds
            //                  since 1 Jan 1970 (a timestamp) 
            //   a string     : Any format supported by the javascript engine, like
            //                  "YYYY/MM/DD", "MM/DD/YYYY", "Jan 31 2009" etc.
            //  an object     : Interpreted as an object with year, month and date
            //                  attributes.  **NOTE** month is 0-11.
            return (
                d.constructor === Date ? d :
                d.constructor === Array ? new Date(d[0],d[1],d[2]) :
                d.constructor === Number ? new Date(d) :
                d.constructor === String ? new Date(d) :
                typeof d === "object" ? new Date(d.year,d.month,d.date) :
                NaN
            );
        },
        compare:function(a,b) {
            // Compare two dates (could be of any type supported by the convert
            // function above) and returns:
            //  -1 : if a < b
            //   0 : if a = b
            //   1 : if a > b
            // NaN : if a or b is an illegal date
            // NOTE: The code inside isFinite does an assignment (=).
            return (
                isFinite(a=this.convert(a).valueOf()) &&
                isFinite(b=this.convert(b).valueOf()) ?
                (a>b)-(a<b) :
                NaN
            );
        },
        inRange:function(d,start,end) {
            // Checks if date in d is between dates in start and end.
            // Returns a boolean or NaN:
            //    true  : if d is between start and end (inclusive)
            //    false : if d is before start or after end
            //    NaN   : if one or more of the dates is illegal.
            // NOTE: The code inside isFinite does an assignment (=).
        return (
                isFinite(d=this.convert(d).valueOf()) &&
                isFinite(start=this.convert(start).valueOf()) &&
                isFinite(end=this.convert(end).valueOf()) ?
                start <= d && d <= end :
                NaN
            );
        }
    };

    const $q = useQuasar()

    const rows = ref([]);
    const id = ref(-1);
    const progress = ref(false);
    const tab = ref('pubMult');
    const search = ref('');
    const email = ref('');
    const date = ref('');
    const dateFinal = ref('');
    const updated = ref(false);

    onMounted(async () => {
      //obter dados do utilizador(podia ser passado como props)
      const result_getAllPostMultimedia = await axios({
        method: "get",
        url: URL.URL + "/posts/postsMultimedia",
      });

      const result_AllPostMultimedia = await result_getAllPostMultimedia.data;

      result_AllPostMultimedia.forEach((p) => {
        const temp = {
            "id": p.id,
            "jogo" : p.jogo,
            "descricao" : p.descricao.substring(0, 40),
            "datetime" : p.datetime,
            "multimedia" : p.multimedia,
            "gamer_id" : p.gamer.id,
            "gamer_nome": p.gamer.nome
        };
        rows.value.push(temp);
      });

    });

    const openNewTab = (link) => {
        window.open(link, "_blank");
    }

    const get_post_multimedia = (async () => {

      rows.value = [];
      
      const result_getAllPostMultimedia = await axios({
        method: "get",
        url: URL.URL + "/posts/postsMultimedia",
      });

      const result_AllPostMultimedia = await result_getAllPostMultimedia.data;

      result_AllPostMultimedia.forEach((p) => {
        const temp = {
            "id": p.id,
            "jogo" : p.jogo,
            "descricao" : p.descricao.substring(0, 40),
            "datetime" : p.datetime,
            "multimedia" : p.multimedia,
            "gamer_id" : p.gamer.id,
            "gamer_nome": p.gamer.nome
        };
        rows.value.push(temp);
      });

    });

    const get_post_Grupo = (async () => {
      
      rows.value = [];

      const result_getAllPostGrupo = await axios({
        method: "get",
        url: URL.URL + "/posts/postsGrupo",
      });

      const result_AllPostGrupo = await result_getAllPostGrupo.data;

      result_AllPostGrupo.forEach((p) => {
        const temp = {
            "id": p.id,
            "jogo" : p.jogo,
            "descricao" : p.descricao.substring(0, 40),
            "datetime" : p.datetime,
            "gamer_id" : p.gamer.id,
            "gamer_nome": p.gamer.nome
        };
        rows.value.push(temp);
      });

    });

    const get_utilizadores = (async () => {
      
      rows.value = [];

      const result_getAllPostMultimedia = await axios({
        method: "get",
        url: URL.URL + "/utilizador/getAllGamers",
      });

      const result_AllPostMultimedia = await result_getAllPostMultimedia.data;

      result_AllPostMultimedia.forEach((p) => {
        const temp = {
            "id": p.id,
            "nome" : p.nome,
            "classificacao" : p.classificacao,
            "avatar" : p.avatar.link
        };
        rows.value.push(temp);
      });

    });

    const changeTab = ( (t) => {

        if(t=='pubMult'){
            get_post_multimedia();
        }else{
            if(t=='pubGrup'){
                get_post_Grupo();
            }else{
                if(t=='Utili'){
                    get_utilizadores();
                }
            }
        }
    });

    const simulateProgress = (async () => {

      const id_post = id.value;
      const tipo_post = (tab.value == "Utili") ? -1 : (tab.value == "pubMult") ? 0 : 1;
      
      loading.value[ id_post ] = true;
      updated.value = !updated.value;
      
      id.value = -1;
      
      let result = false;

      if(tipo_post >= 0){

        const apagarPost = await axios({
            method: "post",
            url: URL.URL + "/posts/deletePost/" + id_post,
            params: {
            'tipo_post': tipo_post,
            }
        });

        result = await apagarPost.data;
      }else{
        
        const apagarUser = await axios({
            method: "post",
            url: URL.URL + "/utilizador/banirGamer/" + id_post
        });

        result = await apagarUser.data;
      }

      if(!result){
          $q.notify({
            color: 'red-5',
            textColor: 'white',
            icon: 'warning',
            message: 'Erro ao apagar (id='+id_post+')'
          })
          loading.value[ id_post ] = false;
          updated.value = !updated.value;
      }else{
          let i = 0;
          while( i < rows.value.length){
              if(rows.value[i].id == id_post){
                rows.value.splice(i, 1);
                i = rows.value.length;
              }
              i++;
          }

          $q.notify({
            color: 'green-4',
            textColor: 'white',
            icon: 'cloud_done',
            message: 'Apagado com sucesso (id='+id_post+')'
          })

          loading.value.delete(id_post);
      }
    });


    const rows_filtered = computed (() => {
        var list = [];

        var identificador = search.value;
        var nome = email.value;
        var temp = updated.value;

        if(tab.value!='Utili'){

            var data_inic = (date.value == "") ? new Date(1900) : new Date(date.value);
            var data_final = (dateFinal.value == "") ? new Date() : new Date(dateFinal.value);

            rows.value.forEach(function (g) {
                
                var dataPublicacao = new Date(g.datetime);

                if(dates.inRange (dataPublicacao, data_inic, data_final)){
                    if (identificador=="" && nome==""){
                        list.push(g);
                    }else{
                        if (identificador==""){
                            if (g.gamer_nome.toLowerCase().includes(nome.toLowerCase())) {
                                list.push(g);
                            }
                        }else{
                            if(nome==""){
                                if (g.id == identificador) {
                                    list.push(g);
                                }
                            }else{
                                if (g.id == identificador && g.gamer_nome.toLowerCase().includes(nome.toLowerCase()) ) {
                                    list.push(g);
                                }
                            }
                        }
                    }
                }
            });
        }else{
            rows.value.forEach(function (g) {
                if (identificador=="" && nome==""){
                    list.push(g);
                }else{
                    if (identificador==""){
                        if (g.nome.toLowerCase().includes(nome.toLowerCase())) {
                            list.push(g);
                        }
                    }else{
                        if(nome==""){
                            if (g.id == identificador) {
                                list.push(g);
                            }
                        }else{
                            if (g.id == identificador && g.nome.toLowerCase().includes(nome.toLowerCase()) ) {
                                list.push(g);
                            }
                        }
                    }
                }
            });
        }

        return list;
    });

    const loading = computed (() => {
        var res = new Map();
        rows.value.forEach(function (g) {
            res[g.id] = false;
        });
        
        return res;
    });

    return {
      id,
      loading,
      persistent: ref(false),
      progress,
      simulateProgress,
      email,
      search,
      date,
      dateFinal,
      columns_Multimedia,
      columns_Grupo,
      columns_Utilizador,
      openNewTab,
      rows,
      changeTab,
      tab,
      rows_filtered,
      updated
    }
  }
}

</script>

<style>

</style>
