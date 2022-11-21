package com.gamehub.Repositories;

import com.gamehub.Model.Users.Gamer;
import org.springframework.data.jpa.repository.Modifying;
import org.springframework.data.jpa.repository.Query;
import org.springframework.data.repository.CrudRepository;
import org.springframework.data.repository.query.Param;
import org.springframework.transaction.annotation.Transactional;

import java.math.BigInteger;
import java.util.List;

public interface GamerRepository extends CrudRepository<Gamer, Integer> {
    Gamer findByNome(String nome);

    String getGamersInConversa = "SELECT caixa_mensagens FROM conversas WHERE gamer=:gamer1 AND caixa_mensagens in (SELECT caixa_mensagens FROM conversas WHERE gamer=:gamer2)";

    String removeFromGroup = "UPDATE gamer SET grupo_id = NULL WHERE grupo_id in (SELECT grupo.id from (grupo INNER JOIN post_grupo on grupo_id=grupo.id and post_grupo.id=:id_post))";

    String deleteFromPossiveisAvaliacoes = "DELETE FROM possiveis_avaliacoes WHERE amigo1=:avaliador AND amigo2=:avaliado";

    String podeAvaliar = " SELECT EXISTS (SELECT * FROM possiveis_avaliacoes WHERE amigo1=:idGamer AND amigo2=:id_amigo)";

    String addAvaliacaoPossivel = "INSERT INTO possiveis_avaliacoes (amigo1, amigo2) VALUES (:gamer1,:gamer2)";


    String deleteGamer = "delete from gamer where id = :id";

    String deleteAmigos = "delete from amigos where amigo1 = :id or amigo2 = :id";

    String deletePossiveisAvaliacoesGamer = "delete from possiveis_avaliacoes" +
            " where amigo1 = :id or amigo2 = :id";

    String deleteRecompensasGamer = "delete from recompensas where gamer = :id";

    String deleteJogosGamer = "delete from jogos where gamer = :id";

    String deleteDislikesGamer = "delete from dislikes where gamer = :id";

    String deleteLikesGamer = "delete from likes where gamer = :id";

    String deletePostMultimediaGamer = "delete from post_multimedia where gamer_id = :id";

    String deletePostMultimediaTagsByGamer = "DELETE pmt.* FROM gamer as g" +
            "    JOIN post_multimedia AS pm ON pm.gamer_id = g.id" +
            "    JOIN post_multimedia_tags AS pmt ON pmt.post_multimedia_id = pm.id" +
            "    WHERE g.id = :id_gamer";

    String deleteLikesPost = "DELETE FROM likes WHERE post = :id";

    String deleteDislikesPost = "DELETE FROM dislikes WHERE post = :id";

    @Modifying
    @Query(value = deleteLikesPost, nativeQuery = true)
    @Transactional
    void deleteLikesPost(@Param("id") int id);


    @Modifying
    @Query(value = deleteDislikesPost, nativeQuery = true)
    @Transactional
    void deleteDislikesPost(@Param("id") int id);

    @Modifying
    @Query(value = deleteDislikesGamer, nativeQuery = true)
    @Transactional
    void deleteDislikesGamer(@Param("id") int id);

    @Modifying
    @Query(value = deleteLikesGamer, nativeQuery = true)
    @Transactional
    void deleteLikesGamer(@Param("id") int id);

    @Modifying
    @Query(value = deletePostMultimediaGamer, nativeQuery = true)
    @Transactional
    void deletePostMultimediaGamer(@Param("id") int id);

    @Modifying
    @Query(value = deleteGamer, nativeQuery = true)
    @Transactional
    void deleteGamer(@Param("id") int id);

    @Modifying
    @Query(value = deleteAmigos, nativeQuery = true)
    @Transactional
    void deleteAmigos(@Param("id") int id);

    @Modifying
    @Query(value = deletePossiveisAvaliacoesGamer, nativeQuery = true)
    @Transactional
    void deletePossiveisAvaliacoesGamer(@Param("id") int id);

    @Modifying
    @Query(value = deleteRecompensasGamer, nativeQuery = true)
    @Transactional
    void deleteRecompensasGamer(@Param("id") int id);

    @Modifying
    @Query(value = deleteJogosGamer, nativeQuery = true)
    @Transactional
    void deleteJogosGamer(@Param("id") int id);

    @Modifying
    @Query(value = removeFromGroup, nativeQuery = true)
    @Transactional
    void removeFromGroup(@Param("id_post") int id_post);

    @Query(value = getGamersInConversa, nativeQuery = true)
    Integer getCaixaMensagemComAmigo(@Param("gamer1") int id_gamer, @Param("gamer2") int id_amigo);

    String getIdsAmigos = "SELECT amigo2 FROM amigos WHERE amigo1 = :id_gamer";

    @Query(value = getIdsAmigos, nativeQuery = true)
    List<Integer> getIdsAmigos(@Param("id_gamer") int id_gamer);

    @Modifying
    @Query(value = deleteFromPossiveisAvaliacoes, nativeQuery = true)
    @Transactional
    void deleteFromPossiveisAvaliacoes(@Param("avaliador") int avaliador, @Param("avaliado") int avaliado);

    @Query(value = podeAvaliar, nativeQuery = true)
    BigInteger podeAvaliar(@Param("idGamer") int idGamer, @Param("id_amigo") int id_amigo);

    @Modifying
    @Query(value = addAvaliacaoPossivel, nativeQuery = true)
    @Transactional
    void addAvaliacaoPossivel(@Param("gamer1") int id, @Param("gamer2") int id_gamer);

    @Modifying
    @Query(value = deletePostMultimediaTagsByGamer, nativeQuery = true)
    @Transactional
    void deletePostMultimediaTags(@Param("id_gamer") int id_gamer);
}
